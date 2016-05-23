(** The main automation tactics. *)
Require Import Program.Tactics.
From Autosubst Require Import Basics Decidable MMap Classes Morphisms.

(** Derived substitution lemmas. *)

Section LemmasForSubst.

  Context {sort : Type}
          {dec_eq_sort : forall a b : sort, Dec (a = b)}
          {Vector_sort : Vector sort}
          {term : sort -> Type}
          {VarConstr_term : VarConstr term} {Rename_term : Rename term} {Subst_term : Subst term}
          {SubstLemmas_term : SubstLemmas term}.

Implicit Types (sigma tau theta :  substitution term) (xi : sort -> var -> var).

Lemma rename_substX xi : rename xi = subst (renV xi).
Proof. repeat(f_ext; intros). now apply rename_subst. Qed.

(* Variable (o : sort) (sigma : vec (fun o : sort => var -> term o)) (s : term o) . *)

(* Goal up o sigma = up o sigma. unfold up. simpl. rewrite rename_substX. simpl. *)

Lemma upX o (sigma : substitution term) :
  up o sigma =
  updV o (Var o 0 .: getV sigma o >> subst (renV (upd o (+1) idr)) (o:=o))
     (sigma |>> subst (renV (upd o (+1) idr))).
Proof. unfold up. now rewrite rename_substX. Qed.

Lemma id_scompX sigma o : ids >> subst sigma (o := o) = getV sigma o.
Proof. f_ext. now eapply id_subst. Qed.

Lemma id_scompR {A} sigma o (f : term o -> A) :
  ids >> (subst sigma (o := o) >> f) = getV sigma o >> f.
Proof. now rewrite <- compA, id_scompX. Qed.

Lemma subst_idX : subst (newV Var) = fun o (s : term o) => s.
Proof. f_ext. intro. f_ext. now eapply subst_id. Qed.

Lemma subst_compI sigma tau o (s : term o) :
  s.|[sigma].|[tau] = s.|[sigma |>> subst tau].
Proof. now eapply subst_comp. Qed.

Lemma subst_compX sigma tau o:
  (^sigma) >>^ tau = subst (sigma |>> subst tau) (o := o).
Proof. f_ext. intro. now eapply subst_comp. Qed.

Lemma subst_compR {A} sigma tau o (f : _ -> A) :
  (^ sigma) >> subst tau (o := o) >> f = (^ sigma |>> subst tau) >> f.
Proof. now rewrite <- subst_compX. Qed.

Lemma fold_ren_cons (x : var) (xi : var -> var) o :
  Var o x .: (xi >> ids) = (x .: xi) >> ids.
Proof. now rewrite scons_comp. Qed.

Lemma fold_comp_ren o (xi zeta : var -> var) : xi >> ren o zeta = ren o (xi >> zeta).
Proof. now rewrite compA. Qed.
(* unfold upn *)

(* Lemma upnSX n sigma : *)
(*   upn (S n) sigma = ids 0 .: upn n sigma >> subst (ren (+1)). *)
(* Proof. *)
(*   unfold iterate; now rewrite upX. *)
(* Qed. *)

(* Lemma upnSE n sigma : *)
(*   upn (S n) sigma = ids 0 .: upn n sigma >> ren (+1). *)
(* Proof. *)
(*   now rewrite upnSX. *)
(* Qed. *)

(* Lemma upn0 sigma : upn 0 sigma = sigma. *)
(* Proof. reflexivity. Qed. *)



(* fold up *)

(* Lemma fold_up k sigma : *)
(*   ids k .: sigma >> ren (+S k) = up sigma >> ren (+k). *)
(* Proof. *)
(*   unfold scomp, ren. rewrite upX; fsimpl; rewrite id_subst, subst_compX; simpl; fsimpl. *)
(*   unfold ren. fsimpl. rewrite id_scompX. now fsimpl. *)
(* Qed. *)

(* Lemma fold_up0 sigma : *)
(*   sigma >> ren (+0) = sigma. *)
(* Proof. *)
(*   unfold scomp, ren. fsimpl. now rewrite subst_idX. *)
(* Qed. *)



(* combine up *)

(* Lemma fold_up_up sigma : up (up sigma) = upn 2 sigma. *)
(* Proof. reflexivity. Qed. *)

(* Lemma fold_up_upn n sigma : up (upn n sigma) = upn (S n) sigma. *)
(* Proof. reflexivity. Qed. *)

(* Lemma fold_upn_up n sigma : upn n (up sigma) = upn (S n) sigma. *)
(* Proof. now rewrite iterate_Sr. Qed. *)

End LemmasForSubst.

Ltac autosubst_typeclass_normalize :=
  mmap_typeclass_normalize;
  repeat match goal with
  | [|- context[ids ?x]] =>
    let s := constr:(ids x) in progress change (ids x) with s
  | [|- context[renV ?xi]] =>
    let s := constr:(renV xi) in progress change (renV xi) with s
  | [|- context[rename ?xi]] =>
    let s := constr:(rename xi) in progress change (rename xi) with s
  | [|- context[subst ?sigma]] =>
    let s := constr:(subst sigma) in progress change (subst sigma) with s
  end.

Ltac autosubst_typeclass_normalizeH H :=
  mmap_typeclass_normalizeH H;
  repeat match typeof H with
  | context[ids ?x] =>
    let s := constr:(ids x) in progress change (ids x) with s in H
  | context[renV ?xi] =>
    let s := constr:(renV xi) in progress change (renV xi) with s in H
  | context[rename ?xi] =>
    let s := constr:(rename xi) in progress change (rename xi) with s in H
  | context[subst ?sigma] =>
    let s := constr:(subst sigma) in progress change (subst sigma) with s in H
  end.


Ltac autosubst_unfold_up :=
  rewrite ?upX (*, ?upnSX; *)
  (* repeat match goal with *)
  (* | [|- context[upn 0 ?sigma]] => change (upn 0 sigma) with sigma *)
  (* end *).

Ltac autosubst_unfold_upH H :=
  rewrite ?upX(* , ?upnSX*) in H(*; *)
  (* repeat match typeof H with *)
  (* | context[upn 0 ?sigma] => change (upn 0 sigma) with sigma *)
  (* end *).

Ltac autosubst_unfoldG :=
  autosubst_typeclass_normalize; autosubst_unfold_up;
  rewrite ?(@rename_substX _ _ _ _ _ _);
  repeat (unfold subst1, renV, upren, updV, newV, funcompV; simpl);
  repeat match goal with [|- context[_ (?VarC ?o ?x)]] => progress change (VarC o x) with (Var o x) end.

Ltac autosubst_unfoldH H :=
  autosubst_typeclass_normalizeH H; autosubst_unfold_upH H;
  rewrite ?(@rename_substX _ _ _ _ _ _) in H;
  repeat (unfold subst1, renV, upren, updV, newV, funcompV in H; simpl in H);
  repeat match typeof H with
         | context[_ (?VarC ?o ?x)] => progress change (VarC o x) with (Var o x) in H end.

(* Ltac autosubst_unfoldH H := *)
(*   autosubst_typeclass_normalizeH H; autosubst_unfold_upH H; *)
(*   rewrite ?(@rename_substX _ _ _ _ _ _) in H; unfold renV, upren, newV in H. *)

Ltac autosubst_foldG :=
  rewrite ?fold_comp_ren, ?fold_ren_cons;
  repeat match goal
         with [|-context[ ?t ]] =>
              match t with ?s.|[?sigma] =>
                           let rec findarg sigma :=
                               first[ replace t with s.[sigma] by reflexivity
                                    | match sigma with (?sigma1, ?sigma2) =>
                                                   first[replace t with s.[sigma1] by reflexivity
                                                        | findarg sigma2]
                                      end]
                           in
                                                       findarg sigma
         end end;
  repeat match goal with |- context[@Var _ _ ?VarC ?o ?x] => change (@Var _ _ VarC o x) with (VarC o x); try unfold VarC end;
  repeat match goal with |- context[?f >> DOM ?R] => change (f >> DOM R) with (DOM f >> R) end.

Ltac autosubst_foldH H :=
  rewrite ?fold_comp_ren, ?fold_ren_cons in H;
  repeat match typeof H with
         | context[ ?t ] =>
           match t with ?s.|[?sigma] =>
                        let rec findarg sigma :=
                            first[ replace t with s.[sigma] in H by reflexivity
                                 | match sigma with (?sigma1, ?sigma2) =>
                                                    first[replace t with s.[sigma1] in H by reflexivity
                                                         | findarg sigma2]
                                   end]
                        in
                        findarg sigma
           end end;
  repeat match typeof H with
         | context[@Var _ _ ?VarC ?o ?x] => change (@Var _ _ VarC o x) with (VarC o x) in H; try unfold VarC in H end;
  repeat match typeof H with
         | context[?f >> DOM ?R] => change (f >> DOM R) with (DOM f >> R) in H end.

Ltac etaReduce := repeat lazymatch goal with [|- context[fun x => ?f x]] => change (fun x => f x) with f end.

Ltac etaReduceH H := repeat lazymatch goal with [H : context[fun x => ?f x] |- _ ] => change (fun x => f x) with f in H end.

(* What is all that folding and unfolding about ? *)
Ltac autosubst_normalizeG :=
  fsimplG; rel_stepG; try
  let subst_idX_inst := fresh "E" in
    lazymatch goal with [|- context[@subst _ _ _ ?Subst_term]] =>
    pose proof (@subst_idX _ _ _ _ _ Subst_term _) as subst_idX_inst;
    unfold newV in subst_idX_inst;
    simpl in subst_idX_inst
  end; repeat first
  [ progress (
      autosubst_unfoldG; fsimplG; rel_stepG; autosubst_unfold_up;
      autorewrite with autosubst;
      rewrite ?id_scompX, ?id_scompR, ?subst_compX,
      ?subst_compR, ?id_subst, ?subst_id, ?subst_compI, ?subst_idX_inst
    )
  | fold_id]; clear subst_idX_inst
.

Ltac autosubst_normalizeH H :=
  fsimplH H; rel_stepH H; try
  let subst_idX_inst := fresh "E" in
    lazymatch typeof H with | context[@subst _ _ _ ?Subst_term] =>
    pose proof (@subst_idX _ _ _ _ _ Subst_term _) as subst_idX_inst;
    unfold newV in subst_idX_inst;
    simpl in subst_idX_inst
end; repeat first
  [ progress (
      autosubst_unfoldH H; fsimplH H; rel_stepH H; autosubst_unfold_upH H;
      autorewrite with autosubst in H;
      rewrite ?id_scompX, ?id_scompR, ?subst_compX,
      ?subst_compR, ?id_subst, ?subst_id, ?subst_compI, ?subst_idX_inst in H
    )
  | fold_idH H]; clear subst_idX_inst
.

Ltac asimplG := autosubst_unfoldG; autosubst_normalizeG; autosubst_foldG.
Ltac asimplH H := autosubst_unfoldH H; autosubst_normalizeH H; autosubst_foldH H.

(* Machinery for asimpl in hypotheses.
  TODO: remove let hiding of evars once asimpl can do this generically. *)

Lemma rbb0 (P Q : Prop) : P -> (let Q' := Q in (P -> Q')) -> Q.
Proof. firstorder. Qed.

(* the "all" prevents [eapply in] from seeing the universal binders. *)
Lemma rbb1 {A : Type} (P Q : A -> Prop) :
  (forall a, P a) -> (let Q' := Q in forall a, P a -> Q' a) -> all Q.
Proof. firstorder. Qed.

Lemma rbb2 {A B : Type} (P Q : A -> B -> Prop) :
  (forall a b, P a b) -> (let Q' := Q in forall a b, P a b -> Q' a b) ->
  all (fun a => forall b, Q a b).
Proof. firstorder. Qed.

Lemma rbb2_dep {A : Type} {B : A -> Type} (P Q : forall a : A, B a -> Prop) :
  (forall a b, P a b) -> (let Q' := Q in forall a b, P a b -> Q' a b) ->
  all (fun a => (forall b, Q a b)).
Proof. firstorder. Qed.

Lemma rbb3 {A B C : Type} (P Q : A -> B -> C -> Prop) :
  (forall a b c, P a b c) ->
  (let Q' := Q in forall a b c, P a b c -> Q' a b c) ->
  all (fun a => (forall b c, Q a b c)).
Proof. firstorder. Qed.

Lemma rbb3_dep
      {A : Type} {B : A -> Type} {C : forall a : A, B a -> Type}
      (P Q : forall (a : A) (b : B a), C a b -> Prop) :
  (forall a b c, P a b c) ->
  (let Q' := Q in forall a b c, P a b c -> Q' a b c) ->
  all (fun a => (forall b c, Q a b c)).
Proof. firstorder. Qed.

Lemma rbb4 {A B C D : Type} (P Q : A -> B -> C -> D -> Prop) :
  (forall a b c d, P a b c d) ->
  (let Q' := Q in forall a b c d, P a b c d -> Q' a b c d) ->
  all (fun a => (forall b c d, Q a b c d)).
Proof. firstorder. Qed.

Lemma rbb4_dep
      {A : Type} {B : A -> Type} {C : forall a : A, B a -> Type} {D : forall (a : A) (b : B a), C a b -> Type}
      (P Q : forall (a : A) (b : B a) (c : C a b), D a b c -> Prop) :
  (forall a b c d, P a b c d) ->
  (let Q' := Q in forall a b c d, P a b c d -> Q' a b c d) ->
  all (fun a => (forall b c d, Q a b c d)).
Proof. firstorder. Qed.

Lemma rbb5 {A B C D E : Type} (P Q : A -> B -> C -> D -> E -> Prop) :
  (forall a b c d e, P a b c d e) ->
  (let Q' := Q in forall a b c d e, P a b c d e -> Q' a b c d e) ->
  all (fun a => (forall b c d e, Q a b c d e)).
Proof. firstorder. Qed.

Lemma rbb5_dep
      {A : Type}
      {B : A -> Type}
      {C : forall a : A, B a -> Type}
      {D : forall (a : A) (b : B a), C a b -> Type}
      {E : forall (a : A) (b : B a) (c : C a b), D a b c -> Type}
      (P Q : forall (a : A) (b : B a) (c : C a b) (d : D a b c), E a b c d -> Prop) :
  (forall a b c d e, P a b c d e) ->
  (let Q' := Q in forall a b c d e, P a b c d e -> Q' a b c d e) ->
  all (fun a => (forall b c d e, Q a b c d e)).
Proof. firstorder. Qed.

Lemma rbb6 {A B C D E F : Type} (P Q : A -> B -> C -> D -> E -> F -> Prop) :
  (forall a b c d e f, P a b c d e f) ->
  (let Q' := Q in forall a b c d e f, P a b c d e f -> Q' a b c d e f) ->
  all (fun a => (forall b c d e f, Q a b c d e f)).
Proof. firstorder. Qed.

Lemma rbb6_dep
      {A : Type}
      {B : A -> Type}
      {C : forall a : A, B a -> Type}
      {D : forall (a : A) (b : B a), C a b -> Type}
      {E : forall (a : A) (b : B a) (c : C a b), D a b c -> Type}
      {F : forall (a : A) (b : B a) (c : C a b) (d : D a b c), E a b c d -> Type}
      (P Q : forall (a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d), F a b c d e -> Prop) :
  (forall a b c d e f, P a b c d e f) ->
  (let Q' := Q in forall a b c d e f, P a b c d e f -> Q' a b c d e f) ->
  all (fun a => (forall b c d e f, Q a b c d e f)).
Proof. firstorder. Qed.

Lemma rbb7 {A B C D E F G : Type} (P Q : A -> B -> C -> D -> E -> F -> G -> Prop) :
  (forall a b c d e f g, P a b c d e f g) ->
  (let Q' := Q in forall a b c d e f g, P a b c d e f g -> Q' a b c d e f g) ->
  all (fun a => (forall b c d e f g, Q a b c d e f g)).
Proof. firstorder. Qed.

Lemma rbb8 {A B C D E F G H : Type} (P Q : A -> B -> C -> D -> E -> F -> G -> H -> Prop) :
  (forall a b c d e f g h, P a b c d e f g h) ->
  (let Q' := Q in forall a b c d e f g h, P a b c d e f g h -> Q' a b c d e f g h) ->
  all (fun a => (forall b c d e f g h, Q a b c d e f g h)).
Proof. firstorder. Qed.

Lemma rbb9 {A B C D E F G H I : Type} (P Q : A -> B -> C -> D -> E -> F -> G -> H -> I -> Prop) :
  (forall a b c d e f g h i, P a b c d e f g h i) ->
  (let Q' := Q in forall a b c d e f g h i, P a b c d e f g h i -> Q' a b c d e f g h i) ->
  all (fun a => (forall b c d e f g h i, Q a b c d e f g h i)).
Proof. firstorder. Qed.

Lemma rbb10 {A B C D E F G H I J: Type} (P Q : A -> B -> C -> D -> E -> F -> G -> H -> I -> J -> Prop) :
  (forall a b c d e f g h i j, P a b c d e f g h i j) ->
  (let Q' := Q in forall a b c d e f g h i j, P a b c d e f g h i j -> Q' a b c d e f g h i j) ->
  all (fun a => (forall b c d e f g h i j, Q a b c d e f g h i j)).
Proof. firstorder. Qed.

Ltac asimplHQ H :=
  lazymatch typeof H with
  | (forall a b c d e f g h i j, (@?T a b c d e f g h i j)) => eapply (@rbb10 _ _ _ _ _ _ _ _ _ _ T) in H
  | (forall a b c d e f g h i, (@?T a b c d e f g h i)) => eapply (@rbb9 _ _ _ _ _ _ _ _ _ T) in H
  | (forall a b c d e f g h, (@?T a b c d e f g h)) => eapply (@rbb8 _ _ _ _ _ _ _ _ T) in H
  | (forall a b c d e f g, (@?T a b c d e f g)) => eapply (@rbb7 _ _ _ _ _ _ _ T) in H
  | (forall a b c d e f, (@?T a b c d e f)) => eapply (@rbb6_dep _ _ _ _ _ _ T) in H
  | (forall a b c d e, (@?T a b c d e)) => eapply (@rbb5_dep _ _ _ _ _ T) in H
  | (forall a b c d, (@?T a b c d)) => eapply (@rbb4_dep _ _ _ _ T) in H
  | (forall a b c, (@?T a b c)) => eapply (@rbb3_dep _ _ _ T) in H
  | (forall a b, (@?T a b)) => eapply (@rbb2_dep _ _ T) in H
  | (forall a, (@?T a)) => eapply (@rbb1 _ T) in H
  | ?T  => eapply (@rbb0 T) in H
  end;
  [|intros; lazymatch goal with H : _ |- _ => revert H end; asimplG; exact id]; unfold all in H.

Ltac asimpl := under_intros idtac (*TODO: asimplH *) asimplG.
Tactic Notation "asimpl" "in" ident(H) := asimplH H.

Tactic Notation "asimpl" "in" "*" := asimplG;
  let m := fresh "marker" in
  pose (m := tt); intros;
  repeat(revert_last; asimplG);
  repeat first[revert m; intros _; fail 1 | intro].


Ltac autosubst := now asimpl.
