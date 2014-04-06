(**
* Generally useful definitions and tactics.
*)

Require Import Coq.Program.Tactics.
Require Import List FunctionalExtensionality.

(** a variant of type of that is stable under import of ssreflect *)
Ltac typeof s := let T := type of s in T.

Ltac f_ext := apply functional_extensionality.

Ltac autorew := repeat match goal with [H : _ |- _] => rewrite H end.

Notation nosimpl t := (let 'tt := tt in t).

Definition id {A} (x : A) := x.
Arguments id {A} x /.
Hint Unfold id.

Lemma conj' (A B : Prop) : A -> (A -> B) -> A /\ B. 
Proof. tauto. Qed.

Definition iter := nosimpl (fix iter {A} (f : A -> A) n a :=
  match n with
    | 0 => a
    | S n' => f(iter f n' a)
  end). 
Arguments iter {A} f n a.

Lemma iter_S {A} (f : A -> A) n a : iter f (S n) a = f (iter f n a).
Proof. reflexivity. Qed.

Lemma iter_0 {A} (f : A -> A) a : iter f 0 a = a.
Proof. reflexivity. Qed.

Ltac autorevert x := 
  try (match goal with
    | [y : ?Y |- ?claim] =>
      try(match x with y => idtac end; fail 1);
        match goal with [z : _ |- _] => 
          match claim with appcontext[z] => 
            first[
                match Y with appcontext[z] => revert y; autorevert x end 
              | match y with z => revert y; autorevert x end]  
          end
        end 
       end).

Tactic Notation "in_all" tactic(T) :=
  repeat match goal with [H : _ |- _] =>
                  first[T H; try revert H | revert H]
  end; intros.

(** A variant of the do tactical that behaves like a limit to repeat *)
Ltac do_try n t := match n with 0 => idtac | S ?n' => try (progress t; do_try n' t) end.
Tactic Notation (at level 3) "do?" constr(n) tactic3(t) := do_try n t. 


Ltac clear_all := repeat match goal with H : _ |- _ => clear H end.
Ltac is_trivial s := try (assert s; [clear_all; (now idtac || fail 1) | fail]).

Ltac clean := 
  (let T H := let s := typeof H in is_trivial s; clear H in
  in_all T); clear_dups.

Ltac inv H := inversion H; try subst; try clear H.

Ltac ainv t :=
  clean;
  do? 10 (idtac; match goal with 
        | H : ?s |- _ =>
            progress( 
                (cut True; [ 
                   inv H; t
                 | ]); [(intros _ || trivial) | now idtac ..]; clean
              ) 
         end).

Tactic Notation "ainv" tactic(t) := ainv t.

Tactic Notation "ainv" := ainv trivial.

(** rename an assumption identified by its type *)

Tactic Notation "ren" ident(H) ":" open_constr(T) := 
match goal with [G : T |- _] =>
  let T' := typeof G in unify T T'; rename G into H end.

Tactic Notation "renc" ident(H) ":" open_constr(T) := 
  match goal with [G : appcontext C [T] |- _] =>
                  let TG := typeof G in
                  let CT := context C [T] in
                  unify TG CT;
                  rename G into H 
  end.


Tactic Notation "eassert" open_constr(T) := assert(T).
Tactic Notation "epose" open_constr(T) := eassert _;[refine T | idtac].

Lemma equal_f {X Y} {f g : X -> Y} a : f = g -> f a = g a. intros. now subst. Qed.


(** Functions and Notations that are useful but not limited to substitutions *)

Delimit Scope subst_scope with subst.
Open Scope subst_scope.

(** ordinary function composition ... *)
Definition funcomp {A B C : Type} (f : A -> B) (g : B -> C) x := g(f(x)).
Arguments funcomp {A B C} f g x /.

(** ... with reversed notation *)
Notation "f >>> g" := (funcomp f g) (at level 55, right associativity) : subst_scope.

Lemma funcomp_assoc A B C D (f : A -> B) (g : B -> C) (h : C -> D): (f >>> g) >>> h = f >>> g >>> h.
Proof. f_ext. reflexivity. Qed.

Lemma id_funcomp A B (f : A -> B) : id >>> f = f.
Proof. f_ext. reflexivity. Qed.

Lemma funcomp_id A B (f : A -> B) : f >>> id = f.
Proof. f_ext. reflexivity. Qed.

(** the cons operation on streams represented as functions from natural numbers *)
Definition scons {X : Type} s sigma x : X := match x with S x' => sigma x' | _ => s end.
Infix ".:" := scons (at level 55, right associativity) : subst_scope.

Lemma funcomp_scons_distr (X Y : Type) (f : X -> Y) (x : X) (xs : nat -> X) : 
  (x .: xs) >>> f = (f x) .: (xs >>> f).
Proof.
  f_ext. now intros [|].
Qed.

(** append a list to a stream *)
Fixpoint sapp {X : Type} (l : list X) (sigma : nat -> X) : nat -> X  := match l with nil => sigma | cons s l' => s .: sapp l' sigma end.
Infix ".++" := sapp (at level 55, right associativity) : subst_scope.
Arguments sapp {_} !l sigma / _.

(* plus with different simplification behaviour *)
Definition lift (x y : nat) : nat := plus x y.
Arguments lift x y/.
Notation "( + x )" := (lift x) (format "( + x )").


(** take a prefix from a stream *)
Fixpoint take {X : Type} n (sigma : nat -> X) : list X := match n with 0 => nil | S n' => sigma 0 :: take n' ((+1) >>> sigma) end.