(**
  Default instances for mmap.
  For ssreflect, you might want to use the library versions instead.
*)
Require Import Autosubst.Basics Autosubst.MMap.

Require List.

Section MMapInstances.

Variable (A B C : Type).
Variable (MMap_A_B : MMap A B).
Variable (MMap_A_C : MMap A C).
Variable (MMapLemmas_A_B : MMapLemmas A B).
Variable (MMapLemmas_A_C : MMapLemmas A C).
Variable (MMapExt_A_B : MMapExt A B).
Variable (MMapExt_A_C : MMapExt A C).

Global Instance MMap_option : MMap A (option B). derive. Defined.
Global Instance MMapLemmas_option : MMapLemmas A (option B). derive. Qed.
Global Instance MMapExt_option : MMapExt A (option B). derive. Defined.

Global Instance MMap_list : MMap A (list B). derive. Defined.
Global Instance MMapLemmas_list : MMapLemmas A (list B). derive. Qed.
Global Instance MMapExt_list : MMapExt A (list B). derive. Defined.

Global Instance MMap_pair : MMap A (B * C). derive. Defined.
Global Instance MMapLemmas_pair : MMapLemmas A (B * C). derive. Qed.
Global Instance MMapExt_pair : MMapExt A (B * C). derive. Defined.

Global Instance MMap_fun : MMap A (B -> C) := fun f g x => mmap f (g x).

Global Instance MMapLemmas_fun : MMapLemmas A (B -> C).
Proof.
  constructor; intros; f_ext; intros; [apply mmap_id|apply mmap_comp].
Qed.

Global Instance MMapExt_fun : MMapExt A (B -> C).
Proof.
  hnf. intros f g H h. f_ext. intro x. apply mmap_ext. exact H.
Defined.

End MMapInstances.
