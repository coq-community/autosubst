Require Import Logic.ClassicalFacts.
Require Import Autosubst.Basics Autosubst.Classes Autosubst.Decidable.

Axiom prop_ext : Coq.Logic.ClassicalFacts.prop_extensionality.

(* JK: level and assoc ok? *)
(* Domain of a relation *)
Notation "'DOM' R" := (R >> @ex _) (at level 56, right associativity).
(* Lifting functions to relations *)
Notation "'REL' f" := (f >> @eq _) (at level 56, right associativity).

Definition subset {A : Type} (P1 P2 : A -> Prop) := forall a, P1 a -> P2 a.
Notation "P :c Q" := (subset P Q) (at level 57, right associativity).

Lemma subset_eq {A : Type} (x : A) P : subset (eq x) P <-> P x.
Proof. split; repeat intro; subst; eauto. Qed.

Lemma subset_refl {A : Type} (P : A -> Prop) : subset P P.
Proof. firstorder. Qed.

Lemma subset_trans {A : Type} (P1 P2 P3 : A -> Prop) :
  subset P1 P2 -> subset P2 P3 -> subset P1 P3.
Proof. firstorder. Qed.

Definition rsubset {A B : Type} (R1 R2 : A -> B -> Prop) := forall a b, R1 a b -> R2 a b.
Notation "R :< S" := (rsubset R S) (at level 57, right associativity).

Lemma rsubset_scons {A : Type} (P1 P2 : A -> Prop) R1 R2 :
  P1 .: R1 :< P2 .: R2  <-> P1 :c P2 /\ R1 :< R2.
Proof.
  split.
  - intros H. split.
    + now specialize (H 0).
    + intro n. now specialize (H (S n)).
  - intros [H1 H2] [|n]; simpl; eauto.
Qed.

(* JK: may require improvement *)
Lemma rsubset_subset {A B : Type} (R1 R2 : A -> B -> Prop): R1 :< R2 -> (DOM R1) :c (DOM R2).
Proof. firstorder. Qed.

(* JK: may require improvement *)
Lemma rsubset_refl {A B : Type} (R : A -> B -> Prop): R :< R.
Proof. firstorder. Qed.

Lemma rsubset_trans {A B : Type} (R1 R2 R3 : A -> B -> Prop) :
  R1 :< R2 -> R2 :< R3 -> R1 :<  R3.
Proof. firstorder. Qed.

(* Definition papp {A B : Type} (R : A -> B -> Prop) P : B -> Prop := fun b => exists a, P a /\ R a b. *)

Definition rapp {A B : Type} (R : A -> B -> Prop) P : B -> Prop := fun b => exists a, P a /\ R a b.

Lemma rapp_eq1 {A : Type} : rapp eq = @id (A -> Prop).
Proof. repeat(f_ext; intro). apply prop_ext. firstorder. now subst. Qed.

Lemma rapp_eq_app {A B : Type} (f g : A -> B) (P : A -> Prop) x : f x = g x -> P x -> rapp (REL f) P (g x).
Proof. firstorder. Qed.

Lemma rapp_eq2 (A B : Type) (R : A -> B -> Prop) x : rapp R (eq x) = R x.
Proof. f_ext. intros. apply prop_ext. firstorder congruence. Qed.

Lemma rapp_rapp {A B C : Type} (R1 : A -> B -> Prop) (R2 : B -> C -> Prop) : rapp R1 >> rapp R2 = rapp (R1 >> rapp R2).
Proof. (repeat (f_ext; intros)). apply prop_ext. firstorder. Qed.

Lemma rapp_ex (A B : Type) (f : A -> B) : DOM rapp (REL f) = @ex A.
Proof. f_ext. intros. apply prop_ext. unfold rapp. simpl. firstorder eauto. Qed.

Definition total {A B : Type} (R : A -> B -> Prop) := forall a : A, exists b : B, R a b. (* Depr. *)

(* JK: may require improvement *)
Lemma sub_rapp_ex {A B C : Type} (R1 : A -> B -> Prop) (R2 : B -> C -> Prop) :
  (DOM (R1 >> rapp R2)) :c (DOM R1).
Proof. firstorder. Qed.

Lemma ex_True {A : Type} y : (exists x : A, y = x) = True.
Proof. apply prop_ext. intuition. now eexists. Qed.

Lemma eq_rapp {A B : Type} (R : A -> B -> Prop) : eq >> rapp R = R.
Proof. repeat( f_ext; intro). apply prop_ext. firstorder congruence. Qed.

Definition rcomp {A B C : Type} (R1 : A -> B -> Prop) (R2 : B -> C -> Prop) : A -> C -> Prop :=
  R1 >> rapp R2.

(* Lemma rcomp_cons {A B : Type} x f (R : A -> B -> Prop) : rcomp (P .: R1) R2 = P .: f >> R. *)

(* JK: may require improvement *)
Lemma rsubset_rcomp {A B C : Type} (R1 R1' : A -> B -> Prop) (R2 R2' : B -> C -> Prop) :
  R1 :< R1' -> R2 :< R2' -> R1 >> rapp R2 :< R1' >> rapp R2'.
Proof. firstorder. Qed.

(* Converse relation; maybe deprecated ...  *)
Definition conv {A B : Type} (R : A -> B -> Prop) := fun b a => R a b.

Lemma rapp_conv {A B : Type} (f : A -> B) :
  rapp (conv (REL f)) = fun P => f >> P.
Proof. repeat (f_ext; intro). apply prop_ext. cbv. firstorder. congruence. Qed.

Definition injectiveF {A B : Type} (f : A -> B) := forall a1 a2 : A, f a1 = f a2 -> a1 = a2.

(* JK: this law requires injectivity of f ... *)
(* Lemma conv_eq {A B : Type} (f : A -> B) (a : A) : *)
(*   injectiveF f -> conv (f >> eq) (f a) = eq a. *)
(* Proof. intros f_inj. f_ext. intros. cbv. apply prop_ext. firstorder; auto. congruence. Qed. *)

Lemma conv_fun_subset {A B : Type} (f : A -> B) (a : A) :
  eq a :c conv (REL f) (f a).
Proof. intros a' Ea; congruence. Qed.

Definition surjectiveR {A B : Type} (R : A -> B -> Prop) := forall b : B, exists a : A, R a b.

Lemma conv_total {A B : Type} (R : A -> B -> Prop) : surjectiveR R -> total (conv R).
Proof. firstorder. Qed.

Definition functional {A B : Type} (R : A -> B -> Prop) := forall a b b', R a b -> R a b' -> b = b'.

Lemma fun_func {A B : Type} (f : A -> B) : functional (REL f).
Proof. intros a b b'. simpl. congruence. Qed.

Lemma preconv_K1 {A B : Type} (R : A-> B -> Prop) : functional R -> conv R >> rapp R :< eq.
Proof. firstorder. Qed.

(* Lemma convK1 {A B : Type} (R : A -> B -> Prop) : *)
(*   surjectiveR R -> functional R -> (conv R) >> rapp R = eq. *)
(* Proof. *)
(*   intros R_surj R_fun. unfold conv. f_ext. intros b. f_ext. intros b'. apply prop_ext. firstorder eauto. *)
(*   simpl. subst. destruct (R_surj b') as [a Ha]. firstorder. *)
(* Qed. *)

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
