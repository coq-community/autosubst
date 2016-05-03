(**  A small library for decidable propositions based on type classes. *)
Require Import Arith.
Require Import Autosubst.Basics.

(* Definition dec (X : Type) : Type := (X + (X -> False))%type. *)
Notation dec X := (X + (X -> False))%type.

Class Dec (X : Type) : Type := decide : dec X.
Arguments decide X {_}.

Tactic Notation "decide" constr(p) := destruct (decide p).

Instance decidable_neg(P : Prop) (DecP : Dec P) : Dec (~P).
decide P. 
+ now right.
+ now left.
Qed.

Ltac eq_dec_decend s t :=
  first[left; congruence
       | right; congruence
       | match s with ?s1 ?s2 => match t with ?t1 ?t2 =>
           decide (s2 = t2);[eq_dec_decend s1 t1 | right; congruence]
         end end
       | idtac].

Ltac derive_Dec_eq_step := cbv; match goal with
                                   |- ((?s = ?t) + _)%type => destruct s; destruct t;
                                                       match goal with |- ((?s = ?t) + _)%type =>
                                                                       eq_dec_decend s t
                                                       end
                               end.




Ltac derive_Dec_eq :=
  repeat intro; match goal with |- Dec(?s = ?t) =>
           revert s t; let H1 := fresh "H" in fix H1 1; intros; try derive_Dec_eq_step
      end.
(*unfold Dec; unfold dec; decide equality; try now apply (decide _).*)
Hint Extern 0 (Dec (_ = _)) => derive_Dec_eq : derive.



Ltac derive_Dec_eq_with T :=
  repeat intro; match goal with |- Dec(?s = ?t) =>
                                revert s t; let H1 := fresh "H" in let H2 := fresh "H" in
                                                                  fix H1 1 with (H2 (s t : T) {struct s} : Dec(s=t)); intros; try derive_Dec_eq_step
      end.


Ltac derive_Dec_eq_with2 T1 T2 :=
  repeat intro; match goal with |- Dec(?s = ?t) =>
                                revert s t; let H1 := fresh "H" in
                                            let H2 := fresh "H" in
                                            let H3 := fresh "H" in
                                            fix H1 1 with (H2 (s t : T1) {struct s} : Dec(s=t))
                                                          (H3 (s t : T2) {struct s} : Dec(s=t));
                                              intros; try derive_Dec_eq_step
                end.

Instance Dec_eq_nat (x y : nat) : Dec (x = y). derive. Defined.

Instance Dec_le_nat (x y : nat) : Dec (x <= y). firstorder using le_dec. Defined.

Instance Dec_lt_nat (x y : nat) : Dec (x < y). firstorder using lt_dec. Defined.

Instance Dec_and (P1 P2 : Prop) {Dec_P1 : Dec P1} {Dec_P2 : Dec P2} : Dec (P1 /\ P2). cbv. decide P1. decide P2; tauto. tauto. Defined.

Instance Dec_or (P1 P2 : Prop) {Dec_P1 : Dec P1} {Dec_P2 : Dec P2} : Dec (P1 \/ P2). cbv. decide P1. tauto. decide P2; tauto. Defined.

Instance Dec_impl (P1 P2 : Prop) {Dec_P1 : Dec P1} {Dec_P2 : Dec P2} : Dec (P1 -> P2). cbv. decide P1. decide P2; tauto. tauto. Defined.


Class Countable (X : Type) := {
                               enum : nat -> X;
                               repr : X -> nat;
                               countableProp : forall x, enum(repr x) = x
                             }. 

Class Finite (X : Type) {CountableX : Countable X} := {
                                                       numElems : nat;
                                                       finiteProp : forall x, repr x < numElems
                                                     }.

Arguments numElems X {_ _}.

Require Import Omega.

Instance Dec_fin_quant_T (P : nat -> Prop) {DecP : forall n, Dec (P n)} (m : nat) : Dec {n | n < m /\ P n}.
cbv. induction m.
- right. firstorder.
- decide (P (m)).
  + firstorder.
  + destruct IHm.
    * firstorder.
    * right. intros [n' H]. decide (n' < m); firstorder.
      now replace n' with m in * by omega.
Defined.

Instance Dec_fin_quant (P : nat -> Prop) {DecP : forall n, Dec (P n)} (m : nat) : Dec (exists n, n < m /\ P n).
destruct (Dec_fin_quant_T P m). left; firstorder. right; firstorder. Defined.

Require Import FunctionalExtensionality.


Lemma decide_eq_fin_domain {X Y : Type} {CountableX : Countable X} {FiniteX : Finite X} {DecEqY : forall (y1 y2 : Y), Dec (y1 = y2)}  (f g : X -> Y) :
  (f = g) + {x | f x <> g x}.
Proof.
  destruct (decide {n | n < numElems _ /\ f (enum n) <> g (enum n)}) as [ H | H].
+ right.
  destruct H as [n [H1 H2]].
  exists (enum n). intros H. auto using equal_f.
+ left. apply functional_extensionality.
  intros x.
  decide (f x = g x); trivial.
  exfalso. apply H. exists (repr x).
  split.
  now eauto using finiteProp.
  now rewrite countableProp.
Defined.
  
Instance Dec_eq_fin_domain {X Y : Type} {CountableX : Countable X} {FiniteX : Finite X} {DecEqY : forall (y1 y2 : Y), Dec (y1 = y2)}  (f g : X -> Y) :
  Dec (f = g).
destruct (decide_eq_fin_domain f g) as [H | H].
+ now left.
+ right. intro. destruct H. congruence.
Defined.