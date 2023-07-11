From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun.
Require Import AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** **** Untyped Lambda Calculus *)

Inductive term : Type :=
| Var (x : var)
| App (s t : term)
| Lam (s : {bind term}).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

(** **** One-Step Reduction *)

Inductive step : term -> term -> Prop :=
| step_beta s t :
    step (App (Lam s) t) s.[t/]
| step_appL s1 s2 t :
    step s1 s2 -> step (App s1 t) (App s2 t)
| step_appR s t1 t2 :
    step t1 t2 -> step (App s t1) (App s t2)
| step_lam s1 s2 :
    step s1 s2 -> step (Lam s1) (Lam s2).

Notation red := (star step).
Notation "s === t" := (conv step s t) (at level 50).

(*
Lemma step_ebeta (s t u : term) : s.[t/] = u -> step (App (Lam s) t) u.
Proof. move<-. exact: step_beta. Qed.

Lemma step_subst sigma s t : step s t -> step s.[sigma] t.[sigma].
Proof.
  move=> st. elim: st sigma => /={s t}; eauto using step.
  move=> s t sigma. apply: step_ebeta. by autosubst.
Qed.
 *)

(** **** Many-Step Reduction *)

Lemma red_app s1 s2 t1 t2 :
  red s1 s2 -> red t1 t2 -> red (App s1 t1) (App s2 t2).
Proof.
  move=> A B. apply: (star_trans (App s2 t1)).
  - apply: (star_hom (App^~ t1)) A => x y. exact: step_appL.
  - apply: star_hom B => x y. exact: step_appR.
Qed.

Lemma red_lam s1 s2 : red s1 s2 -> red (Lam s1) (Lam s2).
Proof. apply: star_hom => x y. exact: step_lam. Qed.

Global Hint Resolve red_app red_lam : red_congr.

(** **** Church-Rosser theorem *)

Inductive pstep : term -> term -> Prop :=
| pstep_beta (s1 s2 t1 t2 : term) :
    pstep s1 s2 -> pstep t1 t2 -> pstep (App (Lam s1) t1) s2.[t2/]
| pstep_var (x : var) :
    pstep (Var x) (Var x)
| pstep_app (s1 s2 t1 t2 : term) :
    pstep s1 s2 -> pstep t1 t2 -> pstep (App s1 t1) (App s2 t2)
| pstep_lam (s1 s2 : term) :
    pstep s1 s2 -> pstep (Lam s1) (Lam s2).

Definition psstep (sigma tau : var -> term) :=
  forall x, pstep (sigma x) (tau x).

Fixpoint rho (s : term) : term :=
  match s with
    | App (Lam s) t => (rho s).[rho t/]
    | App s t => App (rho s) (rho t)
    | Lam s => Lam (rho s)
    | x => x
  end.

Lemma pstep_ebeta s1 s2 t1 t2 u :
  s2.[t2/] = u -> pstep s1 s2 -> pstep t1 t2 -> pstep (App (Lam s1) t1) u.
Proof. move<-. exact: pstep_beta. Qed.

Lemma pstep_refl s : pstep s s.
Proof. elim: s; eauto using pstep. Qed.
Global Hint Resolve pstep_refl.

Lemma step_pstep s t : step s t -> pstep s t.
Proof. elim; eauto using pstep. Qed.

Lemma pstep_red s t : pstep s t -> red s t.
Proof with eauto with red_congr.
  elim=> {s t} //=... move=> s1 s2 t1 t2 _ A _ B.
  apply: (star_trans (App (Lam s2) t2))... exact/star1/step_beta.
Qed.

Lemma pstep_subst sigma s t :
  pstep s t -> pstep s.[sigma] t.[sigma].
Proof with eauto using pstep.
  move=> A. elim: A sigma => /=... move=> s1 s2 t1 t2 _ A _ B sigma.
  eapply pstep_ebeta... by autosubst.
Qed.

Lemma psstep_up sigma tau :
  psstep sigma tau -> psstep (up sigma) (up tau).
Proof.
  move=> A [|n] //=; asimpl. apply: pstep_subst. exact: A.
Qed.

Lemma pstep_compat sigma tau s t :
  psstep sigma tau -> pstep s t -> pstep s.[sigma] t.[tau].
Proof with eauto using pstep, psstep_up.
  move=> A B. elim: B sigma tau A; asimpl...
  move=> s1 s2 t1 t2 _ A _ B sigma tau C.
  apply: (@pstep_ebeta _ (s2.[up tau]) _ (t2.[tau])); asimpl...
Qed.

Lemma pstep_compat_beta s1 s2 t1 t2 :
  pstep s1 s2 -> pstep t1 t2 -> pstep s1.[t1/] s2.[t2/].
Proof.
  move=> A B. by apply: pstep_compat A => -[|].
Qed.

Lemma rho_triangle : triangle pstep rho.
Proof with eauto using pstep.
  move=> s t. elim=> {s t} //=...
  - move=> s1 s2 t1 t2 _ A _ B. exact: pstep_compat_beta.
  - move=> s1 s2 t1 t2 A ih1 _ ih2. case: s1 A ih1 => //=...
    move=> s A ih1. inv A. inv ih1...
Qed.

Theorem church_rosser :
  forall s t, s === t -> joinable red s t.
Proof.
  apply: (cr_method (e2 := pstep) (rho := rho)).
    exact: step_pstep. exact: pstep_red. exact: rho_triangle.
Qed.
