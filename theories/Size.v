Require Import Omega List Program.Equality.
Require Import Lib.

Class Size (A : Type) := size : A -> nat.

Arguments size {A _} !x /.

Ltac derive_Size :=
hnf; match goal with [ |- ?A -> nat] =>
fix size' 1; 
let s := fresh "s" in
intros s;
assert(size_inst : Size A);[exact size' | idtac];
let E := fresh "E" in
destruct s eqn:E;
match goal with 
    [E : s = ?s' |- _] =>
    let rec map s := 
        (match s with 
             ?s1 ?s2 => 
             let size_s1 := map s1 in
             let s2_T := type of s2 in
             let size_s2 := constr:(1 + size s2) in
             constr:(size_s1 + size_s2)
           | _ => constr:(O) end) in 
    let t' := map s' in
    let t'' := eval simpl plus in t' in
    exact (t'')
end
end.

Hint Extern 0 (Size _) => derive_Size : derive.

Lemma size_rec {A : Type} f (x : A) : forall P : A -> Type, (forall x, (forall y, f y < f x -> P y) -> P x) -> P x.
Proof.
  intros P IS. cut (forall n x, f x <= n -> P x). { eauto. } 
  intros n. induction n; intros; apply IS; intros. 
  - omega.
  - apply IHn. omega.
Defined.

Lemma size_ind2 {A B : Type} f g (x : A) (y : B) : forall P : A -> B -> Prop, (forall x1 y1, (forall x2 y2, f x2 < f x1 -> P x2 y2) -> (forall x2 y2, f x2 = f x1 -> g y2 < g y1 -> P x2 y2) -> P x1 y1) -> P x y.
Proof.
  intros P IS. cut (forall n x, f x <= n ->  forall y, P x y). { eauto. } 
  intros n. induction n; intros.
  - apply IS; intros.
    + omega.
    + cut (forall m x, f x = 0 -> forall y, g y <= m -> P x y). { 
        intros H_c. eapply H_c. omega. eauto. } 
      intros m. induction m; intros; apply IS; intros; try  omega.
      apply IHm; omega.
  - apply IS; intros.
    + apply IHn; omega.
    + cut (forall m x y, f x = f x2 -> g y <= m -> P x y). { eauto. }
      intros m. depind m; intros; apply IS; intros; try omega.
      * apply IHn; omega.
      * apply IHn; omega.
      * apply IHm; omega.
Qed.

Ltac sind H := 
let IH := fresh "IH" in
let x := fresh "x" in
induction H as [x IH] using (@size_rec _ size); try rename x into H.

Ltac sizesimpl := repeat(simpl in *; repeat match goal with [|- context[size ?t]] => let s := constr:(size t) in progress change (size t) with s in * end; autorewrite with size in *).

Tactic Notation "somega" := sizesimpl; try omega; now trivial.

Instance size_list (A : Type) (size_A : Size A) : Size (list A). derive. Show Proof. Defined.

Instance size_nat : Size nat := id.

(** A database of facts about the size function *)

Class SizeFact (A : Type) (x : A) (P : Prop)  := size_fact : P.

Arguments size_fact {A} x {P _}.

Lemma size_app (A : Type) (size_A : Size A) l1 l2 : size(app l1 l2) = size l1 + size l2.
Proof. 
  induction l1; simpl; intuition.
Qed.
Hint Rewrite @size_app : size.
Instance size_fact_app (A : Type) (size_A : Size A) l1 l2 : 
  SizeFact _ (app l1 l2) (size(app l1 l2) = size l1 + size l2). 
apply size_app. Qed.

Lemma size_In A (size_A : Size A) (x : A) l : In x l -> size x < size l.
Proof.
  revert x. 
  induction l; intros; simpl in *; intuition subst. 
  - omega.
  - pose (IHl _ H0). omega.
Qed.
Instance size_fact_In (A : Type) (size_A : Size A) x l (x_in_l : In x l): 
  SizeFact _ x (size x < size l). 
now apply size_In. Qed.