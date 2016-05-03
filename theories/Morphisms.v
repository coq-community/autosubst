Require Import Logic.ClassicalFacts.
Require Import Autosubst.Basics Autosubst.Classes Autosubst.Decidable.

Axiom prop_ext : Coq.Logic.ClassicalFacts.prop_extensionality.

Definition subset {A : Type} (P1 P2 : A -> Prop) := forall a, P1 a -> P2 a.

Lemma subset_eq {A : Type} (x : A) P : subset (eq x) P <-> P x.
Proof. split; repeat intro; subst; eauto. Qed.

Definition rsubset {A B : Type} (R1 R2 : A -> B -> Prop) := forall a b, R1 a b -> R2 a b.

Lemma rsubset_scons {A : Type} (P1 P2 : A -> Prop) R1 R2 : rsubset (P1 .: R1) (P2 .: R2) <-> subset P1 P2 /\ rsubset R1 R2.
Proof.
  split.
  - intros H. split.
    + now specialize (H 0).
    + intro n. now specialize (H (S n)).
  - intros [H1 H2] [|n]; simpl; eauto.
Qed.

(* Definition papp {A B : Type} (R : A -> B -> Prop) P : B -> Prop := fun b => exists a, P a /\ R a b. *)

Definition rapp {A B : Type} (R : A -> B -> Prop) P : B -> Prop := fun b => exists a, P a /\ R a b.

Lemma rapp_eq1 {A : Type} : rapp eq = @id (A -> Prop).
Proof. repeat(f_ext; intro). apply prop_ext. firstorder. now subst. Qed.

Lemma rapp_eq_app {A B : Type} (f g : A -> B) (P : A -> Prop) x : f x = g x -> P x -> rapp (f >> eq) P (g x).
Proof. firstorder. Qed.

Lemma rapp_eq2 (A B : Type) (R : A -> B -> Prop) x : rapp R (eq x) = R x.
Proof. f_ext. intros. apply prop_ext. firstorder congruence. Qed.

Lemma rapp_rapp {A B C : Type} (R1 : A -> B -> Prop) (R2 : B -> C -> Prop) : rapp R1 >> rapp R2 = rapp (R1 >> rapp R2).
Proof. (repeat (f_ext; intros)). apply prop_ext. firstorder. Qed.

Lemma rapp_ex (A B : Type) (f : A -> B) : rapp (f >> eq) >> @ex _ = @ex _.
Proof. f_ext. intros. apply prop_ext. unfold rapp. simpl. firstorder eauto. Qed.

Lemma ex_True {A : Type} y : (exists x : A, y = x) = True.
Proof. apply prop_ext. intuition. now eexists. Qed.

Lemma eq_rapp {A B : Type} (R : A -> B -> Prop) : eq >> rapp R = R.
Proof. repeat( f_ext; intro). apply prop_ext. firstorder congruence. Qed.

Definition rcomp {A B C : Type} (R1 : A -> B -> Prop) (R2 : B -> C -> Prop) : A -> C -> Prop :=
  R1 >> rapp R2.

(* Lemma rcomp_cons {A B : Type} x f (R : A -> B -> Prop) : rcomp (P .: R1) R2 = P .: f >> R. *)

Section SubstInstance.

  Context {sort : Type} {dec_eq_sort : forall a b : sort, Dec (a = b)} {Vector_sort : Vector sort}.

  Context  {term : sort -> Type} {VarConstr_term : VarConstr term} {Rename_term : Rename term}
           {Subst_term : Subst term} {SubstLemmas_term : SubstLemmas term}.

  Context {o1 o2 : sort}.

  Fixpoint atn (o1 : sort) (Gamma : list (term o2)) : var -> term o2 -> Prop :=
                 match Gamma with
                 | cons s Gamma' => (eq s.[ren o1 (+1)]) .: rcomp (atn o1 Gamma') (subst1 (ren o1 (+1)) >> eq)
                 | nil => fun _ _ => False
                 end.

End SubstInstance.