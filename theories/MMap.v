Require Import Lib.

(* MMap is a monomorphic variant of Functor *)

Class MMap (A B: Type) := mmap : (A -> A) -> B -> B.
Arguments mmap {A B _} f !s /.

Class MMapExt {A B : Type} (MMap_A_B : MMap A B) := 
  mmap_ext f g : (forall t, f t = g t) -> forall s, mmap f s = mmap g s.
Arguments mmap_ext {A B MMap_A_B MMapExt f g} H s.

Class MMapLemmas `(mmap_instance : MMap) := {
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

Ltac derive_MMapExt := intros ? ? ?; fix 1; destruct 0; msimpl; f_equal; eauto; now rewrite mmap_ext.

Require List.

Instance mmap_refl (A : Type) : MMap A A := id.
Arguments mmap_refl _ {_} f /.
Instance mmap_lemmas_refl (A : Type) : MMapLemmas (mmap_refl A).
constructor; intuition. Qed.
Instance mmap_ext_refl (A : Type) : MMapExt (mmap_refl A).
hnf. eauto. Defined.


Instance mmap_option (A B : Type) (mmap1 : MMap A B) : MMap A (option B).
derive_MMap. Defined.

Instance mmapLemmas_option (A B : Type) (mmap1 : MMap A B) (l1 : MMapLemmas mmap1) : MMapLemmas (mmap_option A B mmap1).
derive_MMapLemmas. Qed.

Instance mmapExt_option (A B : Type) (mmap1 : MMap A B) (l1 : MMapExt mmap1) : MMapExt (mmap_option A B mmap1).
derive_MMapExt. Defined.


Instance mmap_list (A B : Type) (mmap1 : MMap A B) : MMap A (list B).
derive_MMap. Defined.

Instance mmapLemmas_list (A B : Type) (mmap1 : MMap A B) (l1 : MMapLemmas mmap1) : MMapLemmas (mmap_list A B mmap1).
derive_MMapLemmas. Qed.

Instance mmapExt_list (A B : Type) (mmap1 : MMap A B) (l1 : MMapExt mmap1) : MMapExt (mmap_list A B mmap1).
derive_MMapExt. Defined.


Instance mmap_pair (A B C : Type) (mmap1 : MMap A B) (mmap2 : MMap A C): MMap A (B * C).
derive_MMap. Defined.

Instance mmapLemmas_pair (A B C : Type) (mmap1 : MMap A B) (mmap2 : MMap A C) (l1 : MMapLemmas mmap1) (l2 : MMapLemmas mmap2) : MMapLemmas (mmap_pair A B C mmap1 mmap2).
derive_MMapLemmas.
Qed.


Instance mmapExt_pair (A B C : Type) (mmap1 : MMap A B) (mmap2 : MMap A C) (l1 : MMapExt mmap1) (l2 : MMapExt mmap2) : MMapExt (mmap_pair A B C mmap1 mmap2).
derive_MMapExt.
Defined.

Class MMapInv {A B} (mmap_inst : MMap A B) (f : B -> nat) := mmap_inv : forall g x, f (mmap g x) = f x.

Instance mmapInv_length A B (mmap_inst : MMap B A) : MMapInv (mmap_list _ _ mmap_inst) (@length A).
intros ? l.  induction l; simpl; eauto. Qed.