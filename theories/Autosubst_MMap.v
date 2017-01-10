(**
  Apply a function to all instances of a type A occuring in a type B.
  This is used to implement term structures with containers, e.g.

  Inductive term := C (xs : list term)

  By default we provide mmap instances for option, list, pair and
  the codomain of a function. For additional inductive types, there is
  a derive tactic to generate new mmap instances.
*)
Require Import Autosubst_Basics.

Class MMap (A B: Type) := mmap : (A -> A) -> B -> B.
Arguments mmap {A B _} f !s /.

(**
  Extensionality for mmap. This Lemma is uninteresting, as it is implied by
  functional extensionality. However, instances of this class should be
  transparent and take the proof of [[forall t, f t = gt]] as a non-recursive
  argument. This is sufficient to allow the fixpoint checker to lift proofs
  over mmap.
*)
Class MMapExt (A B : Type) `{MMap A B} :=
  mmap_ext : forall f g,
    (forall t, f t = g t) -> forall s, mmap f s = mmap g s.
Arguments mmap_ext {A B H' _ f g} H s : rename. (* JK-TODO: check how this affects existing code? *)

Class MMapLemmas (A B : Type) `{MMap A B} := {
  mmap_id x : mmap id x = x;
  mmap_comp f g x : mmap f (mmap g x) = mmap (g >>> f) x
}.

(** MMap Lemmas *)

Section LemmasForMMap.

Context {A B : Type}.
Context {MMap_Inst : MMap A B} {MMapLemmas_Inst : MMapLemmas A B}.

Lemma mmap_idX : mmap id = id.
Proof. f_ext. exact mmap_id. Qed.

Lemma mmap_compX f g : mmap f >>> mmap g = mmap (f >>> g).
Proof. f_ext. apply mmap_comp. Qed.

Lemma mmap_compR {C} f g (h : _ -> C) :
  mmap f >>> mmap g >>> h = mmap (f >>> g) >>> h.
Proof. now rewrite <- mmap_compX. Qed.

End LemmasForMMap.

(** Identity Instance *)

Section MMapId.
Context {A : Type}.
Global Instance MMap_refl : MMap A A := id.
Global Instance MMapLemmas_refl : MMapLemmas A A. now constructor. Qed.
Global Instance MMapExt_refl : MMapExt A A. hnf. tauto. Defined.
End MMapId.

Arguments MMap_refl _ _ f /.

Lemma mmap_id_instE {A} f : @mmap _ _ (@MMap_refl A) f = f. reflexivity. Qed.


(** Constant Instance: mmap f x just ignores f and leaves x unchanged.
    This instance has low priority so that it is just used if there is
    no alternative.
 *)

Section MMapConst.
Context {A B: Type}.
Global Instance MMap_const : MMap A B | 100 := fun _ => id.
Global Instance MMapLemmas_const : MMapLemmas A A. now constructor. Qed.
Global Instance MMapExt_const : MMapExt A A. hnf. tauto. Defined.
End MMapConst.

Arguments MMap_const _ _ f x /.

Lemma mmap_const_instE {A B} f x : @mmap _ _ (@MMap_const A B) f x = x. reflexivity. Qed.


(** Simplify mmap expressions *)

Ltac mmap_typeclass_normalize :=
  repeat match goal with
  | [|- context[@mmap ?A ?B _ ?f]] =>
     let s := constr:(@mmap A B _ f) in progress change (@mmap A B _ f) with s
  end.

Ltac mmap_typeclass_normalizeH H :=
  repeat match typeof H with
  | context[@mmap ?A ?B _ ?f] =>
     let s := constr:(@mmap A B _ f) in progress change (@mmap A B _ f) with s
  end.

Hint Rewrite @mmap_id_instE @mmap_const_instE : mmap.
Hint Rewrite @mmap_id @mmap_comp @mmap_idX @mmap_compX @mmap_compR
  using exact _ : mmap.

Hint Rewrite @mmap_id_instE @mmap_const_instE : autosubst.
Hint Rewrite @mmap_id @mmap_comp @mmap_idX @mmap_compX @mmap_compR
  using exact _ : autosubst.

Ltac msimpl :=
  mmap_typeclass_normalize;
  repeat first
  [ solve [trivial]
  | progress (simpl; autorewrite with mmap)
  | fold_id].

Ltac msimplH H :=
  mmap_typeclass_normalizeH H;
  repeat first
  [ solve [trivial]
  | progress (simpl; autorewrite with mmap in H)
  | fold_id in H].

Tactic Notation "msimpl" "in" ident(H) := msimplH H.
Tactic Notation "msimpl" "in" "*" := (in_all msimplH); msimpl.

(** Deriving Instances *)

Ltac derive_MMap :=
  let map := fresh "dummy" in (* hack due to potential ltac bug ! *)
  hnf; match goal with [ |- (?A -> ?A) -> ?B -> ?B ] =>
    intros f; fix map 1; intros xs; change (annot B xs); destruct xs;
    match goal with
      | [ |- annot _ ?ys ] =>
        let rec tmap xs :=
            (match xs with
               | ?s1 ?s2 =>
                 let s1 := tmap s1 in
                 let T  := typeof s2 in
                 let s2 :=
                     match T with
                       | A => constr:(f s2)
                       | B => constr:(map s2)
                       | _ => constr:(mmap f s2)
                     end in
                 constr:(s1 s2)
               | _ => xs
             end) in
        let ys := tmap ys in exact ys
    end
  end.
Hint Extern 0 (MMap _ _) => derive_MMap : derive.

Ltac derive_MMapLemmas := constructor;
  [ induction 0; simpl; f_equal; trivial; apply mmap_id
  | intros f g; induction 0; simpl; f_equal; trivial; apply mmap_comp ].
Hint Extern 0 (MMapLemmas _ _) => derive_MMapLemmas : derive.

Ltac derive_MMapExt :=
  intros ???; fix 1; destruct 0; simpl; f_equal; auto using mmap_ext.
Hint Extern 0 (MMapExt _ _) => derive_MMapExt : derive.

(* Local Variables: *)
(* coq-load-path: (("." "Autosubst")) *)
(* End: *)
