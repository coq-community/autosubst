(** The main automation tactics. *)
Require Import Autosubst_Basics Autosubst_MMap Autosubst_Classes.

(** Derived substitution lemmas. *)

Section LemmasForSubst.

Context {term : Type} {Ids_term : Ids term}
        {Rename_term : Rename term} {Subst_term : Subst term}
        {SubstLemmas_term : SubstLemmas term}.

Implicit Types (s t : term) (sigma tau theta : var -> term) (xi : var -> var).

Lemma rename_substX xi : rename xi = subst (ren xi).
Proof. f_ext. apply rename_subst. Qed.

Lemma upX sigma : up sigma = ids 0 .: sigma >>> subst (ren (+1)).
Proof. unfold up. now rewrite rename_substX. Qed.

Lemma id_scompX sigma : ids >>> subst sigma = sigma.
Proof. f_ext. apply id_subst. Qed.

Lemma id_scompR {A} sigma (f : _ -> A) :
  ids >>> (subst sigma >>> f) = sigma >>> f.
Proof. now rewrite <- compA, id_scompX. Qed.

Lemma subst_idX : subst ids = id.
Proof. f_ext. exact subst_id. Qed.

Lemma subst_compI sigma tau s :
  s.[sigma].[tau] = s.[sigma >>> subst tau].
Proof. apply subst_comp. Qed.

Lemma subst_compX sigma tau :
  subst sigma >>> subst tau = subst (sigma >>> subst tau).
Proof. f_ext. apply subst_comp. Qed.

Lemma subst_compR {A} sigma tau (f : _ -> A) :
  subst sigma >>> (subst tau >>> f) = subst (sigma >>> subst tau) >>> f.
Proof. now rewrite <- subst_compX. Qed.

Lemma fold_ren_cons (x : var) (xi : var -> var) :
  ids x .: ren xi = ren (x .: xi).
Proof. unfold ren. now rewrite scons_comp. Qed.

Lemma upE sigma : up sigma = ids 0 .: sigma >> ren (+1).
Proof. apply upX. Qed.

(* unfold upn *)

Lemma upnSX n sigma :
  upn (S n) sigma = ids 0 .: upn n sigma >>> subst (ren (+1)).
Proof.
  unfold iterate; now rewrite upX.
Qed.

Lemma upnSE n sigma :
  upn (S n) sigma = ids 0 .: upn n sigma >> ren (+1).
Proof.
  now rewrite upnSX.
Qed.

Lemma upn0 sigma : upn 0 sigma = sigma.
Proof. reflexivity. Qed.

(* fold up *)

Lemma fold_up k sigma :
  ids k .: sigma >> ren (+S k) = up sigma >> ren (+k).
Proof.
  unfold scomp, ren. rewrite upX; fsimpl; rewrite id_subst, subst_compX; simpl; fsimpl.
  unfold ren. fsimpl. rewrite id_scompX. now fsimpl.
Qed.

Lemma fold_up0 sigma :
  sigma >> ren (+0) = sigma.
Proof.
  unfold scomp, ren. fsimpl. now rewrite subst_idX.
Qed.

(* combine up *)

Lemma fold_up_up sigma : up (up sigma) = upn 2 sigma.
Proof. reflexivity. Qed.

Lemma fold_up_upn n sigma : up (upn n sigma) = upn (S n) sigma.
Proof. reflexivity. Qed.

Lemma fold_upn_up n sigma : upn n (up sigma) = upn (S n) sigma.
Proof. now rewrite iterate_Sr. Qed.

End LemmasForSubst.

(** Derived substitution lemmas for heterogeneous substitutions. *)

Section LemmasForHSubst.

Context {inner outer : Type}.

Context {Ids_inner : Ids inner} {Rename_inner : Rename inner}
  {Subst_inner : Subst inner} {SubstLemmas_inner : SubstLemmas inner}.

Context {Ids_outer : Ids outer} {Rename_outer : Rename outer}
  {Subst_outer : Subst outer} {SubstLemmas_outer : SubstLemmas outer}.

Context {HSubst_inner_outer : HSubst inner outer}.
Context {HSubstLemmas_inner_outer : HSubstLemmas inner outer}.
Context {SubstHSubstComp_inner_outer : SubstHSubstComp inner outer}.

Lemma id_hsubstX (sigma : var -> inner) : ids >>> hsubst sigma = ids.
Proof. f_ext. apply id_hsubst. Qed.

Lemma id_hsubstR {A} (f : _ -> A) (sigma : var -> inner) :
  ids >>> (hsubst sigma >>> f) = ids >>> f.
Proof. now rewrite <- compA, id_hsubstX. Qed.

Lemma hsubst_idX : hsubst ids = id.
Proof. f_ext. exact hsubst_id. Qed.

Lemma hsubst_compI sigma tau s :
  s.|[sigma].|[tau] = s.|[sigma >>> subst tau].
Proof. apply hsubst_comp. Qed.

Lemma hsubst_compX sigma tau :
  hsubst sigma >>> hsubst tau = hsubst (sigma >>> subst tau).
Proof. f_ext. apply hsubst_comp. Qed.

Lemma hsubst_compR {A} sigma tau (f : _ -> A) :
  hsubst sigma >>> (hsubst tau >>> f) = hsubst (sigma >>> subst tau) >>> f.
Proof. now rewrite <- hsubst_compX. Qed.

Lemma scomp_hcompI sigma theta s :
  s.[sigma].|[theta] = s.|[theta].[sigma >>> hsubst theta].
Proof. apply subst_hsubst_comp. Qed.

Lemma scomp_hcompX sigma theta :
  subst sigma >>> hsubst theta = hsubst theta >>> subst (sigma >>>hsubst theta).
Proof. f_ext. apply subst_hsubst_comp. Qed.

Lemma scomp_hcompR {A} sigma theta (f : _ -> A) :
  subst sigma >>> (hsubst theta >>> f) =
  hsubst theta >>> (subst (sigma >>> hsubst theta) >>> f).
Proof. now rewrite <- compA, scomp_hcompX. Qed.

End LemmasForHSubst.

(** Normalize the goal state. *)

Ltac autosubst_typeclass_normalize :=
  mmap_typeclass_normalize;
  repeat match goal with
  | [|- context[ids ?x]] =>
    let s := constr:(ids x) in progress change (ids x) with s
  | [|- appcontext[ren ?xi]] =>
    let s := constr:(ren xi) in progress change (ren xi) with s
  | [|- appcontext[rename ?xi]] =>
    let s := constr:(rename xi) in progress change (rename xi) with s
  | [|- appcontext[subst ?sigma]] =>
    let s := constr:(subst sigma) in progress change (subst sigma) with s
  | [|- appcontext[hsubst ?sigma]] =>
    let s := constr:(hsubst sigma) in progress change (hsubst sigma) with s
  end.

Ltac autosubst_typeclass_normalizeH H :=
  mmap_typeclass_normalizeH H;
  repeat match typeof H with
  | context[ids ?x] =>
    let s := constr:(ids x) in progress change (ids x) with s in H
  | appcontext[ren ?xi] =>
    let s := constr:(ren xi) in progress change (ren xi) with s in H
  | appcontext[rename ?xi] =>
    let s := constr:(rename xi) in progress change (rename xi) with s in H
  | appcontext[subst ?sigma] =>
    let s := constr:(subst sigma) in progress change (subst sigma) with s in H
  | appcontext[hsubst ?sigma] =>
    let s := constr:(hsubst sigma) in progress change (hsubst sigma) with s in H
  end.

Ltac autosubst_unfold_up :=
  rewrite ?upX, ?upnSX;
  repeat match goal with
  | [|- context[upn 0 ?sigma]] => change (upn 0 sigma) with sigma
  end.

Ltac autosubst_unfold_upH H :=
  rewrite ?upX, ?upnSX in H;
  repeat match typeof H with
  | context[upn 0 ?sigma] => change (upn 0 sigma) with sigma
  end.

Ltac autosubst_unfold :=
  autosubst_typeclass_normalize; autosubst_unfold_up;
  rewrite ?rename_substX, ?upX; unfold ren, scomp, hcomp.

Ltac autosubst_unfoldH H :=
  autosubst_typeclass_normalizeH H; autosubst_unfold_upH H;
  rewrite ?rename_substX, ?upX in H; unfold ren, scomp, hcomp in H.

(** Simplify results. *)

Ltac fold_ren :=
  repeat match goal with
    | [|- context[?xi >>> (@ids ?T _)]] =>
         change (xi >>> (@ids T _)) with (@ren T _ xi)
    | [|- context[?xi >>> (@ids ?T _ >>> ?g)]] =>
         change (xi >>> (@ids T _ >>> g)) with (@ren T _ xi >>> g)
    | [|- context[?xi >>> @ren ?T _ ?zeta]] =>
         change (xi >>> @ren T _ zeta) with (@ren T _ (xi >>> zeta))
    | [|- context[?xi >>> (@ren ?T _ ?zeta >>> ?g)]] =>
         change (xi >>> (@ren T _ zeta >>> g)) with
                (@ren T _ (xi >>> zeta) >>> g)
    | _ => rewrite fold_ren_cons
  end.

Ltac fold_renH H :=
  repeat match typeof H with
    | context[?xi >>> (@ids ?T _)] =>
         change (xi >>> (@ids T _)) with (@ren T _ xi) in H
    | context[?xi >>> (@ids ?T _ >>> ?g)] =>
         change (xi >>> (@ids T _ >>> g)) with (@ren T _ xi >>> g) in H
    | context[?xi >>> @ren ?T _ ?zeta] =>
         change (xi >>> @ren T _ zeta) with (@ren T _ (xi >>> zeta)) in H
    | context[?xi >>> (@ren ?T _ ?zeta >>> ?g)] =>
         change (xi >>> (@ren T _ zeta >>> g)) with
                (@ren T _ (xi >>> zeta) >>> g) in H
    | _ => rewrite fold_ren_cons in H
  end.

Ltac fold_comp :=
  repeat match goal with
    | [|- context[?f >>> (?g >>> ?h)]] =>
        change (f >>> (g >>> h)) with ((f >>> g) >>> h)
    | [|- context[?sigma >>> subst ?tau]] =>
        change (sigma >>> subst tau) with (sigma >> tau)
    | [|- context[?sigma >>> hsubst ?tau]] =>
        change (sigma >>> hsubst tau) with (sigma >>| tau)
  end.

Ltac fold_compH H :=
  repeat match typeof H with
    | context[?f >>> (?g >>> ?h)] =>
        change (f >>> (g >>> h)) with ((f >>> g) >>> h) in H
    | context[?sigma >>> subst ?tau] =>
        change (sigma >>> subst tau) with (sigma >> tau) in H
    | context[?sigma >>> hsubst ?tau] =>
        change (sigma >>> hsubst tau) with (sigma >>| tau) in H
  end.

Ltac fold_up := rewrite ?fold_up, ?fold_up0;
  repeat match goal with
    | [|- context[up (up ?sigma)]] =>
      change (up (up sigma)) with (upn 2 sigma)
    | [|- context[up (upn ?n ?sigma)]] =>
      change (up (upn n sigma)) with (upn (S n) sigma)
    | _ => rewrite fold_upn_up
  end.

Ltac fold_upH H := rewrite ?fold_up, ?fold_up0 in H;
  repeat match typeof H with
    | context[up (up ?sigma)] =>
      change (up (up sigma)) with (upn 2 sigma) in H
    | context[up (upn ?n ?sigma)] =>
      change (up (upn n sigma)) with (upn (S n) sigma) in H
    | _ => rewrite fold_upn_up in H
  end.

(** Solve & Simplify goals involving substitutions. *)

Ltac autosubst :=
  simpl; trivial; autosubst_unfold; solve [repeat first
  [ solve [trivial]
  | progress (
      simpl; unfold _bind, ren, scomp, hcomp; fsimpl; autosubst_unfold_up;
      autorewrite with autosubst;
      rewrite ?id_scompX, ?id_scompR, ?subst_idX, ?subst_compX,
              ?subst_compR, ?id_subst, ?subst_id, ?subst_compI,
              ?id_hsubstX, ?id_hsubstR, ?hsubst_idX, ?scomp_hcompX,
              ?scomp_hcompR, ?hsubst_compX, ?hsubst_compR,
              ?hsubst_id, ?id_hsubst, ?hsubst_compI, ?scomp_hcompI
    )
  | match goal with [|- appcontext[(_ .: _) ?x]] =>
      match goal with [y : _ |- _ ] => unify y x; destruct x; simpl @scons end
    end
  | fold_id]].

Ltac asimpl :=
  simpl; autosubst_unfold; repeat first
  [ progress (
      simpl; unfold _bind, ren, scomp, hcomp; fsimpl; autosubst_unfold_up;
      autorewrite with autosubst;
      rewrite ?id_scompX, ?id_scompR, ?subst_idX, ?subst_compX,
              ?subst_compR, ?id_subst, ?subst_id, ?subst_compI,
              ?id_hsubstX, ?id_hsubstR, ?hsubst_idX, ?scomp_hcompX,
              ?scomp_hcompR, ?hsubst_compX, ?hsubst_compR,
              ?hsubst_id, ?id_hsubst, ?hsubst_compI, ?scomp_hcompI
    )
  | fold_id];
  fold_ren; fold_comp; fold_up.

Ltac asimplH H :=
  simpl in H; autosubst_unfoldH H; repeat first
  [ progress (
      simpl in H; unfold _bind, ren, scomp, hcomp in H; fsimpl in H;
      autosubst_unfold_upH H; autorewrite with autosubst in H;
      rewrite ?id_scompX, ?id_scompR, ?subst_idX, ?subst_compX,
              ?subst_compR, ?id_subst, ?subst_id, ?subst_compI,
              ?id_hsubstX, ?id_hsubstR, ?hsubst_idX, ?scomp_hcompX,
              ?scomp_hcompR, ?hsubst_compX, ?hsubst_compR,
              ?hsubst_id, ?id_hsubst, ?hsubst_compI, ?scomp_hcompI in H
    )
  | fold_id in H];
  fold_renH H; fold_compH H; fold_upH H.

Tactic Notation "asimpl" "in" ident(H) := asimplH H.
Tactic Notation "asimpl" "in" "*" := (in_all asimplH); asimpl.

(* Local Variables: *)
(* coq-load-path: (("." "Autosubst")) *)
(* End: *)
