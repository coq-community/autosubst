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
  | [|- appcontext[renV ?xi]] =>
    let s := constr:(renV xi) in progress change (renV xi) with s
  | [|- appcontext[rename ?xi]] =>
    let s := constr:(rename xi) in progress change (rename xi) with s
  | [|- appcontext[subst ?sigma]] =>
    let s := constr:(subst sigma) in progress change (subst sigma) with s
  end.

Ltac autosubst_typeclass_normalizeH H :=
  mmap_typeclass_normalizeH H;
  repeat match typeof H with
  | context[ids ?x] =>
    let s := constr:(ids x) in progress change (ids x) with s in H
  | appcontext[renV ?xi] =>
    let s := constr:(renV xi) in progress change (renV xi) with s in H
  | appcontext[rename ?xi] =>
    let s := constr:(rename xi) in progress change (rename xi) with s in H
  | appcontext[subst ?sigma] =>
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

Ltac etaReduce := repeat lazymatch goal with [|- context[fun x => ?f x]] => change (fun x => f x) with f end.

Ltac etaReduceH H := repeat lazymatch goal with [H : context[fun x => ?f x] |- _ ] => change (fun x => f x) with f in H end.

(* What is all that folding and unfolding about ? *)
Ltac autosubst_normalizeG :=
  fsimplG; try
  let subst_idX_inst := fresh "E" in
    lazymatch goal with [|- appcontext[@subst _ _ _ ?Subst_term]] =>
    pose proof (@subst_idX _ _ _ _ _ Subst_term _) as subst_idX_inst;
    unfold newV in subst_idX_inst;
    simpl in subst_idX_inst
  end; repeat first
  [ progress (
      autosubst_unfoldG; fsimpl; autosubst_unfold_up; (* ??? why *)
      autorewrite with autosubst;
      rewrite ?id_scompX, ?id_scompR, ?subst_compX,
      ?subst_compR, ?id_subst, ?subst_id, ?subst_compI, ?subst_idX_inst,
      ?rapp_eq1, ?rapp_eq2, ?rapp_rapp, ?eq_rapp, ?rapp_ex, ?ex_True
      (* repeat match goal with [|- appcontext[@subst ?sort ?vec ?term ?Subst ?sigma]] => *)
      (*                        replace (@subst sort vec term Subst sigma ) with (fun o : sort =>  @id (term o)) by eauto using subst_idX end *)
    )
  | fold_id]; clear subst_idX_inst
.

Ltac asimplG := autosubst_unfoldG; autosubst_normalizeG; autosubst_foldG.

(* Ltac asimplH H := *)
(*   simpl in H; autosubst_unfoldH H; repeat first *)
(*   [ progress ( *)
(*         simpl in H; *)
(*         unfold _bind, renV, funcompV in H; fsimplH H; *)
(*         autosubst_unfold_upH H; *)
(*         autorewrite with autosubst in H; *)
(*         rewrite ?id_scompX, ?id_scompR, ?subst_compX, *)
(*         (* ?subst_compR, *) ?id_subst, ?subst_id in H; *)
(*         repeat setoid_rewrite subst_compI in H; *)
(*         let E := constr:(@subst_idX _ _ _ _ _ _) in rewrite ?(E _ _) in H (* I have no idea why this works ... well, it does no longer in Coq 8.5*) *)
(*       ) *)
(*   | fold_idH H](* ; *) *)
(* (* fold_ren; fold_comp; fold_up *). *)



Ltac asimpl := under_intros idtac (*TODO: asimplH *) asimplG.
(*Tactic Notation "asimpl" "in" ident(H) := asimplH H. *)
Tactic Notation "asimpl" "in" "*" := asimplG;
  let m := fresh "marker" in
  pose (m := tt); intros;
  repeat(revert_last; asimplG);
  repeat first[revert m; intros _; fail 1 | intro].


Ltac autosubst := now asimpl.
