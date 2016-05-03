Require Import Autosubst.Basics Autosubst.Decidable.


Notation sort1 := unit (only parsing).
Notation Sort1_1 := tt (only parsing).

Existing Class unit.
Existing Instance tt.

Instance decide_eq_unit (o1 o2 : unit) : Dec (o1 = o2).
  left. now destruct o1, o2. Defined.

Instance Vector_unit : Vector unit :=
  {
    vec T := T _;
    getV T v o := match o with tt => v end;
    newV T f := f tt
  }.
Proof. intros. f_ext. now intros[]. Defined.


Inductive sort2 := Sort1_2 | Sort2_2.

Instance decide_eq_sort2 (o1 o2 : sort2) : Dec (o1 = o2). derive. Defined.

Instance Vector_sort2 : Vector sort2 :=
  {
    vec := (fun T => T Sort1_2 * T Sort2_2)%type;
    getV T v := let (v1, v2) := v in
               fun o => match o with
                         | Sort1_2 => v1
                         | Sort2_2 => v2
                       end;
    newV T f := (f Sort1_2, f Sort2_2)
  }.
Proof. intros. f_ext. now destruct 0. Defined.

