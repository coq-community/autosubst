
(**
  Functions, Notations and Tactics that are useful, but not limited to
  substitutions.
*)

From Coq.Program Require Import Tactics.
From Coq Require Import PeanoNat List FunctionalExtensionality.

(** Annotate "a" with additional information. *)
Definition annot {A B} (a : A) (b : B) : A := a.

(** A variant of type of that is stable under import of ssreflect. *)
Ltac typeof s := let T := type of s in T.

(** Apply a tactic T in all assumptions. *)
Tactic Notation "in_all" tactic(T) :=
  repeat match goal with
  | [H : _ |- _] => first[T H; try revert H | revert H]
  end; intros.

(** Shorthand for functional extensionality. *)
Ltac f_ext := apply functional_extensionality.


(**
  A variant of the Coq [fold] tactic that works with open terms.
  For example, [repeat open_fold (f _).] tries to undo [unfold f] for
  a defined function [f] with a single argument.
*)
Tactic Notation "open_fold" open_constr(s) :=
  let s' := (eval red in s) in
  replace s' with s by reflexivity.

Tactic Notation "open_fold" open_constr(s) "in" hyp(H) :=
  let s' := (eval red in s) in
  replace s' with s  in H by reflexivity.


(** Wrapper for deriving type class instances. *)
Ltac derive := trivial with derive; fail.

(** Assert that type class instance exists.*)
Ltac require_instance s :=
  try (first[
              assert s;[exact _|idtac]
            | fail 10 "The instance" s "is missing"
            ]; fail).

(**
  General automation tactics.
  - "autorew": Tries to rewrite with any equation in the context.
  - "autorevert h": Reverts the assumption h along with all of its
    dependencies.
  - "inv h": Does an inversion on h and cleans up the goal.
  - "ainv": Inverts any assumptions where inv produces only a single
    non-trivial subgoal. Takes a tactic as an optional arguments which is
    used to solve trivial subgoals. Defaults to "ainv trivial".
    Subgoals
  - "ren H: T": Search the context for an assumption which matches the
    pattern T and renames it to H.
  - "renc H: T": Same as above, but tries to match a subterm against T.
*)

Ltac autorew :=
  repeat match goal with
    | [H : _ = _ |- _] => rewrite H
    | [H : forall _, _ |- _] => progress rewrite H by now trivial
  end.

Ltac autorevert x :=
  try (match goal with
    | [y : ?Y |- ?claim] =>
      try (match x with y => idtac end; fail 1);
        match goal with [z : _ |- _] =>
          match claim with context[z] =>
            first
              [ match Y with context[z] => revert y; autorevert x end
              | match y with z => revert y; autorevert x end]
          end
        end
  end).

(** A variant of the do tactical that behaves like a limit to repeat *)
Ltac do_try n t :=
  match n with 0 => idtac | S ?n' => try (progress t; do_try n' t) end.
Tactic Notation (at level 3) "do?" constr(n) tactic3(t) := do_try n t.

Ltac clear_all := repeat match goal with H : _ |- _ => clear H end.
Ltac is_trivial s :=
  try (assert s; [clear_all; (now idtac || fail 1) | fail]).

Ltac clean :=
  (let T H := let s := typeof H in is_trivial s; clear H in
   in_all T); clear_dups.

Ltac inv H := inversion H; try clear H; try subst.

(* JK: IMPORTANT: This tactic appears to rely on the order in which hypothesis are tried during a match goal, and the default order in which hypotheses are matched appears to have changed from 8.5 to 8.6! the [reverse] keyword reinstates the old behaviour but it might be better to reimplement the tactic in a more predictable fashion! this would probably have a significant impact on existing code! *)
Ltac ainv t :=
  clean;
  do? 10 (idtac; match reverse goal with
    | H : ?s |- _ =>
      progress((cut True; [inv H; t|]);
        [(intros _ || trivial) | now idtac ..]; clean)
  end).



Tactic Notation "ainv" tactic(t) := ainv t.
Tactic Notation "ainv" := ainv trivial.

(** rename an assumption identified by its type *)

Tactic Notation "ren" ident(H) ":" open_constr(T) :=
  match goal with
    | [G : T |- _] => let T' := typeof G in unify T T'; rename G into H
  end.

Tactic Notation "renc" ident(H) ":" open_constr(T) :=
  match goal with
    | [G : context C [T] |- _] =>
        let TG := typeof G in
        let CT := context C [T] in
          unify TG CT;
          rename G into H
  end.

Tactic Notation "eassert" open_constr(T) := assert(T).
Tactic Notation "epose" open_constr(T) := eassert _;[refine T | idtac].

(**
  The identity function, and tactics for replacing functions which are
  convertible to id with id. This is important for rewriting, where we
  can only match against terms syntactically. Using the tactic "fold_id"
  ensures that we do not miss functions which are merely convertible to
  "id".
*)

Definition id {A} (x : A) := x.
Arguments id {A} x /.
Global Hint Unfold id : core.

Ltac fold_id :=
  repeat match goal with
    | [|- context [?s]] =>
      match s with (fun _ : ?T => _) => progress (change s with (@id T)) end
  end.

Ltac fold_idH H :=
  repeat match typeof H with
    | context[?s] =>
      match s with
        (fun _ : ?T => _) => progress (change s with (@id T) in H)
      end
  end.

Tactic Notation "fold_id" "in" ident(H) := fold_idH H.
Tactic Notation "fold_id" "in" "*" := (in_all fold_idH); fold_id.

(** Primitives *)

(** A type synonym for natural numbers used as de Bruijn indices *)
Definition var := nat.

Definition iterate := fix iterate {A} (f : A -> A) n a :=
  match n with
    | 0 => a
    | S n' => f(iterate f n' a)
  end.
Arguments iterate {A} f n a : simpl never.

(** ordinary function composition ... *)

Definition funcomp {A B C : Type} (f : A -> B) (g : B -> C) x := g(f(x)).
Arguments funcomp {A B C} f g x /.

(** ... with reversed notation *)

Declare Scope subst_scope.
Delimit Scope subst_scope with subst.
Open Scope subst_scope.

Reserved Notation "sigma >> tau" (at level 56, left associativity).
Notation "f >>> g" := (funcomp f g)
  (at level 56, left associativity) : subst_scope.

(**
  The cons operation on streams represented as functions from natural numbers
*)
Definition scons {X : Type} (s : X) (sigma : var -> X) (x : var) : X :=
  match x with S y => sigma y | _ => s end.
Notation "s .: sigma" := (scons s sigma) (at level 55, sigma at level 56, right associativity) : subst_scope.

(** A test and demonstration of the precedence rules, which effectively declare scons and
    funcomp at the same level, with scons being right associative and funcomp being left
    associative *)
Local Definition parse_test := fun (f : var -> var) (sigma : var -> list var) =>
        nil .: nil .: f >>> f >>> nil .: nil .: f >>> f >>> nil .: nil .: sigma.

(* plus with different simplification behaviour *)
Definition lift (x y : var) : var := plus x y.
Arguments lift x y/.
Notation "( + x )" := (lift x) (format "( + x )").

(*
(*
  WIP: It is currently not clear what the right primitives for binders with
  variable arity should be. The two functions below may be useful.
*)

(** append a list to a stream *)
Fixpoint sapp {X : Type} (l : list X) (sigma : nat -> X) : nat -> X :=
  match l with nil => sigma | cons s l' => s .: sapp l' sigma end.
Infix ".++" := sapp (at level 55, right associativity) : subst_scope.
Arguments sapp {_} !l sigma / _.

(** take a prefix from a stream *)
Fixpoint take {X : Type} n (sigma : nat -> X) : list X :=
  match n with 0 => nil | S n' => sigma 0 :: take n' ((+1) >>> sigma) end.
*)

(** Lemmas for working with the above primitives. *)

Lemma id_comp {A B} (f : A -> B) : id >>> f = f. reflexivity. Qed.
Lemma comp_id {A B} (f : A -> B) : f >>> id = f. reflexivity. Qed.
Lemma compA {A B C D} (f : A -> B) (g : B -> C) (h : C -> D) :
  (f >>> g) >>> h = f >>> (g >>> h).
Proof. reflexivity. Qed.

Section LemmasForFun.

Context {A B : Type}.
Implicit Types (x : A) (f : var -> A) (g : A -> B) (n m : var).

Lemma scons_comp x f g : (x .: f) >>> g = (g x) .: f >>> g.
Proof. f_ext; let x := fresh in intros x; now destruct x. Qed.

Lemma plusSn n m : S n + m = S (n + m). reflexivity. Qed.
Lemma plusnS n m : n + S m = S (n + m). symmetry. apply plus_n_Sm. Qed.
Lemma plusOn n : O + n = n. reflexivity. Qed.
Lemma plusnO n : n + O = n. symmetry. apply plus_n_O. Qed.
Lemma plusA n m k : n + (m + k) = (n + m) + k. apply Nat.add_assoc. Qed.

Lemma scons_eta f n : f n .: (+S n) >>> f = (+n) >>> f.
Proof.
  f_ext; intros [|m]; simpl; [now rewrite plusnO|now rewrite plusnS].
Qed.

Lemma lift0 : (+0) = id. reflexivity. Qed.

Lemma lift_scons x f n : (+S n) >>> (x .: f) = (+n) >>> f.
Proof. reflexivity. Qed.

Lemma lift_comp n m : (+n) >>> (+m) = (+m+n).
Proof. f_ext; intros x; simpl. now rewrite plusA. Qed.

Lemma lift_compR n m f : (+n) >>> ((+m) >>> f) = (+m+n) >>> f.
Proof. now rewrite <- lift_comp. Qed.

End LemmasForFun.

Lemma lift_eta n : n .: (+S n) = (+ n).
Proof. apply (scons_eta id). Qed.

(** Automation for the above *)

Ltac fsimpl :=
  repeat match goal with
    | [|- context[id >>> ?f]] => change (id >>> f) with f
    | [|- context[?f >>> id]] => change (f >>> id) with f
    | [|- context[(?f >>> ?g) >>> ?h]] =>
        change ((f >>> g) >>> h) with (f >>> (g >>> h))
    | [|- context[(+0)]] => change (+0) with (@id var)
    | [|- context[0 + ?m]] => change (0 + m) with m
    | [|- context[?s S]] => change (s S) with (s (+1))
    | [|- context[S ?n + ?m]] => change (S n + m) with (S (n + m))
    | [|- context[(+S ?n) >>> (?x .: ?xr)]] =>
        change ((+S n) >>> (x .: xr)) with ((+n) >>> xr)
    | [|- context[?x .: (+ S ?n) >>> ?f]] =>
        change x with (f n); rewrite (@scons_eta _ f n)
    | _ => progress (rewrite ?scons_comp, ?plusnS, ?plusnO, ?plusA,
                             ?lift_comp, ?lift_compR, ?lift_eta)
  end.

Ltac fsimplH H :=
  repeat match typeof H with
    | context[id >>> ?f] => change (id >>> f) with f in H
    | context[?f >>> id] => change (f >>> id) with f in H
    | context[(?f >>> ?g) >>> ?h] =>
        change ((f >>> g) >>> h) with (f >>> (g >>> h)) in H
    | context[(+0)] => change (+0) with (@id var) in H
    | context[0 + ?m] => change (0 + m) with m in H
    | context[?s S] => change (s S) with (s (+1)) in H
    | context[S ?n + ?m] => change (S n + m) with (S (n + m)) in H
    | context[(+S ?n) >>> (?x .: ?xr)] =>
        change ((+S n) >>> (x .: xr)) with ((+n) >>> xr) in H
    | context[?x .: (+ S ?n) >>> ?f] =>
        change x with (f n) in H; rewrite (@scons_eta _ f n) in H
    | _ => progress (rewrite ?scons_comp, ?plusnS, ?plusnO, ?plusA,
                             ?lift_comp, ?lift_compR, ?lift_eta in H)
  end.

Tactic Notation "fsimpl" "in" ident(H) := fsimplH H.
Tactic Notation "fsimpl" "in" "*" := (in_all fsimplH); fsimpl.

(** Misc Lemmas *)

Lemma iterate_S {A} (f : A -> A) n a : iterate f (S n) a = f (iterate f n a).
Proof. reflexivity. Qed.

Lemma iterate_0 {A} (f : A -> A) a : iterate f 0 a = a.
Proof. reflexivity. Qed.

Lemma iterate_Sr {A} (f : A -> A) n a : iterate f (S n) a = iterate f n (f a).
Proof.
  revert a; induction n. reflexivity. intros a.
  rewrite !iterate_S, <- IHn. reflexivity.
Qed.

Lemma equal_f {X Y} {f g : X -> Y} a : f = g -> f a = g a.
Proof. intros. now subst. Qed.

(* Local Variables: *)
(* coq-load-path: (("." "Autosubst")) *)
(* End: *)
