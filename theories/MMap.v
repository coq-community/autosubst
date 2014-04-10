Require Import Lib.

(* MMap is a monomorphic variant of Functor *)

Class MMap (A B: Type) := mmap : (A -> A) -> B -> B.
Arguments mmap {A B _} f !s /.

Class MMapExt (A B : Type) {MMap_A_B : MMap A B} := 
  mmap_ext f g : (forall t, f t = g t) -> forall s, mmap f s = mmap g s.
Arguments mmap_ext {A B MMap_A_B MMapExt f g} H s.

Class MMapLemmas (A B : Type) {mmap_instance : MMap A B} := {
  mmap_id : mmap id = id;
  mmap_comp x f g: mmap f (mmap g x) = mmap (g >>> f) x
}.

Ltac derive_MMap :=
hnf; match goal with [ |- (?A -> ?A) -> ?B -> ?B] =>
fix mmap' 2; intros f; intros s;
pose(mmap' : MMap A B);
destruct s eqn:E;
let term := typeof s in
match goal with 
    [E : s = ?s' |- _] =>
    let rec map s := 
        (match s with 
             ?s1 ?s2 => 
             let s1' := map s1 in
             let s2_T := typeof s2 in
             let s2' := match s2_T with 
                         | A => constr:(f s2) 
                         | _ => constr:(mmap f s2)
                       end in
             constr:(s1' s2')
           | _ => s end) in 
    let t' := map s' in 
    exact t'
end
end.

Hint Extern 0 (MMap _ _) => derive_MMap : derive.


Hint Rewrite @mmap_id @mmap_comp using exact _ : mmap.
Hint Rewrite @mmap_id @mmap_comp using exact _ : ssimpl.

Ltac msimpl := 
repeat(
     simpl;
     repeat match goal with [|- context[fun _ : ?T => _] ] => 
              progress change (fun s0 : T => s0) with (@id T) 
            end;
     try(autorewrite with mmap; [idtac | now eauto with typeclass_instances ..])
    ); trivial.

Ltac msimplH H := 
repeat(
     simpl in H;
     try(autorewrite with mmap in H; [idtac | now eauto with typeclass_instances ..])
    ); trivial.

Tactic Notation "msimpl" "in" ident(H) := msimplH H.

Tactic Notation "msimpl" "in" "*" := (in_all msimplH); msimpl.

Ltac derive_MMapLemmas :=
constructor;[
f_ext; induction 0; simpl; autorew; now msimpl |
let x := fresh "x" in intros x; induction x; intros; simpl; autorew; now msimpl].

Hint Extern 0 (MMapLemmas _ _) => derive_MMapLemmas : derive.


Ltac derive_MMapExt := intros ? ? ?; fix 1; destruct 0; msimpl; f_equal; eauto; now rewrite mmap_ext.

Hint Extern 0 (MMapExt _ _) => derive_MMapExt : derive.



Require List.

Section MMapInstances.

Variable (A B C : Type).
Variable (MMap_A_B : MMap A B).
Variable (MMap_A_C : MMap A C).
Variable (MMapLemmas_A_B : MMapLemmas A B).
Variable (MMapLemmas_A_C : MMapLemmas A C).
Variable (MMapExt_A_B : MMapExt A B).
Variable (MMapExt_A_C : MMapExt A C).

Global Instance mmap_refl: MMap A A := id.
Arguments mmap_refl _ f /.
Global Instance mmap_lemmas_refl : MMapLemmas A A. constructor; intuition. Qed.
Global Instance mmap_ext_refl : MMapExt A A. hnf. eauto. Defined.

Global Instance mmap_option : MMap A (option B). derive. Defined.
Global Instance mmapLemmas_option : MMapLemmas A (option B). derive. Qed.
Global Instance mmapExt_option : MMapExt A (option B). derive. Defined.

Global Instance mmap_list : MMap A (list B). derive. Defined.
Global Instance mmapLemmas_list : MMapLemmas A (list B). derive. Qed.
Global Instance mmapExt_list : MMapExt A (list B). derive. Defined.


Global Instance mmap_pair : MMap A (B * C). derive. Defined.
Global Instance mmapLemmas_pair : MMapLemmas A (B * C). derive. Qed.
Global Instance mmapExt_pair : MMapExt A (B * C). derive. Defined.

End MMapInstances.

Class MMapInv A {B} {mmap_inst : MMap A B} (f : B -> nat) := mmap_inv : forall g x, f (mmap g x) = f x.

Instance mmapInv_length A B (mmap_inst : MMap A B) : MMapInv A (@length B).
intros ? l.  induction l; simpl; eauto. Qed.