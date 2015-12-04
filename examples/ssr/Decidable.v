(** * Notation for decidable propositions *)
Require Import Arith.

Definition dec (X : Prop) : Type := {X} + {~ X}.
Class Dec (X : Prop) : Type := decide : dec X.
Arguments decide X {_}.

Ltac gen_Dec_eq := unfold Dec; unfold dec; decide equality.

Instance decide_eq_nat (x y : nat) : Dec (x = y). gen_Dec_eq. Defined.

Instance decide_le_nat (x y : nat) : Dec (x <= y). apply le_dec. Defined.

Instance decide_lt_nat (x y : nat) : Dec (x < y). apply lt_dec. Defined.

Tactic Notation "decide" constr(p) := destruct (decide p).