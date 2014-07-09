(** * POPLmark Part 1

    The #<a href="http://www.seas.upenn.edu/~plclub/poplmark/">POPLmark</a>#
    challenge is a set of benchmark problems to evaluate approaches to the
    formalization of syntactic theories.  We solve part 1, that is,
    progress and preservation of System F with subtyping.  *)

Require Import Program.Equality List.
Require Import Autosubst Size Decidable Context.

Inductive type : Type :=
| TyVar (x : var)
| Top
| Arr (A1 A2 : type)
| All (A1 : type) (A2 : {bind type}).

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.

Instance SubstLemmas_type : SubstLemmas type. derive. Qed.

Instance size_type : Size type.
  assert(Size var). exact(fun _ => 0). derive.
Defined.

Inductive term :=
| TeVar (x : var)
| Abs (A : type) (s : {bind term})
| App (s t : term)
| TAbs (A : type) (s : {bind type in term})
| TApp (s : term) (A : type).

Instance hsubst_term : HSubst type term. derive. Defined.

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.

Instance HSubstLemmas_term : HSubstLemmas type term. derive. Qed.

Instance SubstHSubstComp_type_term : SubstHSubstComp type term. derive. Qed.

Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Instance size_term : Size term.
  assert(Size var). exact(fun _ => 0). derive.
Defined.

Lemma ren_size_inv (A : type) : forall xi, size A.[ren xi] = size A.
Proof.
  induction A; intros; sizesimpl; repeat(asimpl; try autorew); somega.
Qed.

Fixpoint wf_ty Delta A := match A with
  | TyVar x => exists B, atnd Delta x B
  | Top => True
  | Arr A B => wf_ty Delta A /\ wf_ty Delta B
  | All A B => wf_ty Delta A /\ wf_ty (A :: Delta) B
end.

Reserved Notation "'SUB' Delta |- A <: B"
  (at level 68, A at level 99, no associativity).
Inductive sub (Delta : list type) : type -> type -> Prop :=
| SA_Top A :
    wf_ty Delta A -> SUB Delta |- A <: Top
| SA_Refl x :
    wf_ty Delta (TyVar x) -> SUB Delta |- TyVar x <: TyVar x
| SA_Trans x A B :
    atnd Delta x A -> SUB Delta |- A <: B -> SUB Delta |- TyVar x <: B
| SA_Arrow A1 A2 B1 B2 :
    SUB Delta |- B1 <: A1 -> SUB Delta |- A2 <: B2 ->
    SUB Delta |- Arr A1 A2 <: Arr B1 B2
| SA_All A1 A2 B1 B2 :
    SUB Delta |- B1 <: A1 -> wf_ty Delta B1 -> SUB (B1 :: Delta) |- A2 <: B2 ->
    SUB Delta |- All A1 A2 <: All B1 B2
where "'SUB' Delta |- A <: B" := (sub Delta A B).

Lemma wf_weak Delta1 Delta2 A xi :
  wf_ty Delta1 A ->
  (forall x B, atnd Delta1  x B -> exists B', atnd Delta2 (xi x) B') ->
  wf_ty Delta2 A.[ren xi].
Proof.
  autorevert A. induction A; intros; ainv; simpl; eauto.
  asimpl. split; eauto.
  eapply IHA0. eassumption.
  intros. ainv (asimpl; eauto using @atnd).
  edestruct H0; eauto. eauto using @atnd.
Qed.

Lemma wf_weak1 Delta A A' B :
  wf_ty Delta A -> A' = A.[ren(+1)] -> wf_ty (B :: Delta) A'.
Proof. intros. subst. eauto using wf_weak, @atnd. Qed.

Corollary wf_weak' Delta1 Delta2 A :
  wf_ty Delta1 A ->
  (length Delta1 <= length Delta2) ->
  wf_ty Delta2 A.
Proof.
  intros. replace A with A.[ren id] by now autosubst.
  eapply wf_weak; eauto.
  intros. apply atnd_defined.
  cut(id x < length Delta1). omega.
  apply atnd_defined. eauto.
Qed.

Lemma sub_refl Delta A : wf_ty Delta A -> SUB Delta |- A <: A.
Proof.
  revert Delta. induction A; simpl; intuition;
  constructor; simpl; eauto using sub.
Qed.

Lemma sub_weak Delta1 Delta2 A1 A2 A1' A2' xi : SUB Delta1 |- A1 <: A2 ->
  (forall x B, atnd Delta1 x B -> atnd Delta2 (xi x) B.[ren xi]) ->
  A1' = A1.[ren xi] -> A2' = A2.[ren xi] ->
  SUB Delta2 |- A1' <: A2' .
Proof.
   intros H. intros. subst. autorevert H.
   induction H; intros; simpl; try now (econstructor; simpl; ainv eauto).
   - eauto using sub, wf_weak.
   - econstructor; asimpl; eauto using wf_weak.
     apply IHsub2.
     intros [|]; intros; asimpl; ainv; econstructor; eauto; now autosubst.
Qed.

Lemma sub_weak1 Delta A A' B B' C :
  SUB Delta |- A <: B ->  A' = A.[ren(+1)] ->  B' = B.[ren(+1)] ->
  SUB (C :: Delta) |- A' <: B'.
Proof.  intros. eapply sub_weak; eauto using @atnd. Qed.

Lemma sub_wf {Delta A B} :
  SUB Delta |- A <: B -> wf_ty Delta A /\ wf_ty Delta B.
Proof.
  intros H. induction H; ainv; simpl; eauto using wf_weak'.
Qed.

Lemma sub_wf_1 Delta A B : SUB Delta |- A <: B -> wf_ty Delta A.
Proof. apply sub_wf. Qed.


Lemma sub_wf_2 Delta A B : SUB Delta |- A <: B -> wf_ty Delta B.
Proof. apply sub_wf. Qed.

Lemma sub_trans' n :
  (forall Delta A B C, n = size B ->
     SUB Delta |- A <: B -> SUB Delta |- B <: C -> SUB Delta |- A <: C) /\
  (forall Delta' Delta B B' A C, n = size B ->
     SUB Delta' ++ B :: Delta |- A <: C ->
     SUB Delta |- B' <: B ->
     SUB Delta' ++ B' :: Delta |- A <: C).
Proof.
  induction n as [n IH] using (size_rec (fun x => x)).
  apply conj'.
  {
    intros Delta A B C ? H_AB H_BC. subst.
    revert C H_BC.
    induction H_AB; intros; ainv; eauto using sub.
    - inv H_BC.
      + constructor. simpl. split; eauto using sub_wf_1, sub_wf_2.
      + constructor; eapply IH; eauto; somega.
    - inv H_BC.
      + constructor; constructor.
        * eapply sub_wf; now eauto.
        * eapply wf_weak'. now eapply (sub_wf H_AB2). now simpl.
      + rename B0 into C1. rename B3 into C2.
        constructor; eauto.
        * eapply IH; eauto; somega.
        * eapply IH; eauto; try somega.
          refine (proj2 (IH _ _) nil _ _ _ _ _ _ _ _); eauto; somega.
  }
  {
    intros H_trans Delta' Delta B B' A C ? H H_B'B. subst.
    revert B' H_B'B.
    depind H; intros; simpl in *.
    - constructor.
      eapply wf_weak'. eassumption.
      repeat rewrite app_length. simpl. omega.
    - constructor. simpl.
      apply atnd_defined. apply atnd_defined in H.
      repeat rewrite -> app_length in *. simpl in *. omega.
    - decide (x = length Delta').
      + subst.
        econstructor. { apply atnd_repl. }
        apply atnd_steps' with (x := 0) in H.
        destruct H as [? [? H]]. inv H.
        eapply H_trans;[idtac | eapply sub_weak;
          try reflexivity; try eassumption | idtac].
        * now rewrite ren_size_inv.
        * intros. change (B' :: Delta) with ((B' :: nil) ++ Delta).
          rewrite app_assoc.
          cutrewrite (S (length Delta') = length (Delta' ++ B' :: nil)).
          now apply atnd_steps.
          rewrite app_length. simpl. omega.
        * asimpl in IHsub.
          eapply IHsub; now eauto.
      + econstructor; eauto.
        eapply atnd_repl; now eauto.
    - constructor; now eauto.
    - constructor.
      + now eauto.
      + eapply wf_weak'. eassumption.
        repeat rewrite app_length. simpl. omega.
      + change (B1 :: Delta' ++ B' :: Delta)
          with ((B1 :: Delta') ++ B' :: Delta).
        eapply IHsub2; eauto. reflexivity.
  }
Qed.

Corollary sub_trans Delta A B C:
  SUB Delta |- A <: B -> SUB Delta |- B <: C -> SUB Delta |- A <: C.
Proof. intros. eapply sub_trans'; eauto. Qed.

Corollary sub_narrow Delta' Delta B B' A C :
     SUB Delta' ++ B :: Delta |- A <: C ->
     SUB Delta |- B' <: B ->
     SUB Delta' ++ B' :: Delta |- A <: C.
Proof. intros. eapply sub_trans'; eauto. Qed.

Inductive value : term -> Prop :=
| Value_Abs A s : value(Abs A s)
| Value_TAbs A s : value(TAbs A s).

Reserved Notation "'TY' Delta ; Gamma |- A : B"
  (at level 68, A at level 99, no associativity,
   format "'TY'  Delta ; Gamma  |-  A  :  B").
Inductive ty (Delta Gamma : list type) : term -> type -> Prop :=
| T_Var A x :
    atn Gamma x A ->
    TY Delta;Gamma |- TeVar x : A
| T_Abs A B s:
    TY Delta;A::Gamma |- s : B   ->   wf_ty Delta A   ->
    TY Delta;Gamma |- Abs A s : Arr A B
| T_App A B s t:
    TY Delta;Gamma |- s : Arr A B   ->   TY Delta;Gamma |- t : A   ->
    TY Delta;Gamma |- App s t : B
| T_TAbs A B s :
    TY A::Delta ; Gamma..[ren(+1)] |- s : B   ->   wf_ty Delta A   ->
    TY Delta;Gamma |- TAbs A s : All A B
| T_TApp A B A' s B' :
    TY Delta;Gamma |- s : All A B ->
    SUB Delta |- A' <: A -> B' = B.[A'/] ->
    TY Delta;Gamma |- TApp s A' : B'
| T_Sub A B s :
    TY Delta;Gamma |- s : A   ->   SUB Delta |- A <: B   ->
    TY Delta;Gamma |- s : B
where "'TY' Delta ; Gamma |- s : A" := (ty Delta Gamma s A).

Reserved Notation "'EV' s => t"
  (at level 68, s at level 80, no associativity, format "'EV'   s  =>  t").
Inductive eval : term -> term -> Prop :=
| E_AppAbs A s t : EV App (Abs A s) t => s.[t/]
| E_TAppTAbs A s B : EV TApp (TAbs A s) B => s.|[B/]
| E_AppFun s s' t :
     EV s => s' ->
     EV App s t => App s' t
| E_AppArg s s' v:
     EV s => s' -> value v ->
     EV App v s => App v s'
| E_TypeFun s s' A :
     EV s => s' ->
     EV TApp s A => TApp s' A
where "'EV' s => t" := (eval s t).


Lemma ty_weak  xi zeta Delta1 Delta2 Gamma1 Gamma2 s A :
  TY Delta1;Gamma1 |- s : A ->
  (forall x B, atnd Delta1 x B -> atnd Delta2 (xi x) B.[ren xi]) ->
  (forall x B, atn Gamma1 x B -> atn Gamma2 (zeta x) B.[ren xi]) ->
  TY Delta2;Gamma2 |- s.|[ren xi].[ren zeta] : A.[ren xi] .
Proof.
   intros H. autorevert H. induction H; intros; simpl.
   - econstructor; now eauto.
   - asimpl. econstructor.
     + apply IHty; eauto. intros x C H_C.
       destruct x; simpl in *; subst; eauto.
     + eauto using wf_weak.
   - asimpl; econstructor; simpl; eauto; apply IHty1; eauto.
   - asimpl. econstructor. apply IHty.
     + intros. now eapply up_atnd; eauto.
     + intros. eapply up_mmap_atn; eauto.
     + eauto using wf_weak.
   - econstructor.
     + simpl in IHty. apply IHty; eauto.
     + eauto using sub_weak.
     + subst. autosubst.
   - eauto using ty, sub_weak.
Qed.

Lemma ty_weak_ty  xi Delta1 Delta2 Gamma1 Gamma2 s s' A A':
  TY Delta1;Gamma1 |- s : A ->
  (forall x B, atnd Delta1 x B -> atnd Delta2 (xi x) B.[ren xi]) ->
  (forall x B, atn Gamma1 x B -> atn Gamma2 x B.[ren xi]) ->
  A' = A.[ren xi] ->
  s' = s.|[ren xi] ->
  TY Delta2;Gamma2 |- s' : A'.
Proof.
  intros. subst. cutrewrite(s.|[ren xi] = s.|[ren xi].[ren id]).
  eapply ty_weak; eauto. now autosubst.
Qed.

Lemma ty_weak_ty' Delta Gamma s s' A A' B:
  TY Delta;Gamma |- s : A ->
  A' = A.[ren (+1)] ->
  s' = s.|[ren (+1)] ->
  TY B::Delta ; Gamma..[ren(+1)] |- s' : A'.
Proof.
  intros. eapply ty_weak_ty; eauto; intros.
  - econstructor; eauto.
  - eapply atn_mmap; eauto.
Qed.

Lemma ty_weak_ter xi Delta Gamma1 Gamma2 s A :
  TY Delta;Gamma1 |- s : A ->
  (forall x B, atn Gamma1 x B -> atn Gamma2 (xi x) B) ->
  TY Delta;Gamma2 |- s.[ren xi] : A.
Proof.
  intros.
  cutrewrite (s = s.|[ren id]).
  cutrewrite (A = A.[ren id]).
  eapply ty_weak; eauto; intros; asimpl; now eauto.
  autosubst. autosubst.
Qed.

Lemma ty_weak_ter1 Delta Gamma s s' A B :
  TY Delta;Gamma |- s : A ->
  s' = s.[ren(+1)] ->
  TY Delta ; B::Gamma |- s' : A.
Proof.
  intros. subst. eapply ty_weak_ter; eauto.
Qed.

Lemma ty_narrow Delta2 Delta1 Gamma A B C s:
  TY Delta2 ++ B :: Delta1 ; Gamma |- s : C  ->
  SUB Delta1 |- A <: B  ->
  TY Delta2 ++ A :: Delta1 ; Gamma |- s : C.
Proof.
  intros H. depind H; econstructor; eauto using ty.
  - eapply wf_weak'. eassumption. repeat rewrite app_length. simpl. omega.
  - change (A0 :: Delta2 ++ A :: Delta1) with ((A0 :: Delta2) ++ A :: Delta1).
    eapply IHty. reflexivity. assumption.
  - eapply wf_weak'. eassumption. repeat rewrite app_length. simpl. omega.
  - now eapply sub_narrow; eauto.
  - now eapply sub_narrow; eauto.
Qed.

Lemma wf_subst Delta1 Delta2 A sigma :
  wf_ty Delta1 A ->
  (forall x B, atnd Delta1 x B -> wf_ty Delta2 (sigma x)) ->
  wf_ty Delta2 A.[sigma].
Proof.
  intros H. autorevert A. induction A; eauto; intros; asimpl.
  - ainv; eauto.
  - ainv; eauto.
  - split. ainv; eauto. ainv. eapply IHA0. eassumption.
    intros [|]; intros.
    + simpl. eauto using @atnd.
    + ainv. asimpl. eapply wf_weak; eauto using @atnd.
Qed.

Lemma sub_subst Delta1 Delta2 A B sigma:
  SUB Delta1 |- A <: B ->
  (forall x C, atnd Delta1 x C -> SUB Delta2 |- sigma x <: C.[sigma]) ->
  SUB Delta2 |- A.[sigma] <: B.[sigma].
Proof.
  intros H. autorevert H.
  induction H; intros; simpl; try econstructor; asimpl;
  eauto using sub, wf_subst, sub_wf_1.
  - inv H. eauto using sub_refl, wf_subst, sub_wf_1.
  - eauto using sub_trans.
  - apply IHsub2. intros. inv H3.
    + econstructor. eauto using @atnd.
      asimpl. apply sub_refl.
      eapply wf_weak1; eauto using sub_wf_1. autosubst.
    + asimpl. eapply sub_weak1; try reflexivity; eauto. autosubst.
Qed.

Lemma ty_subst Delta1 Delta2 Gamma1 Gamma2 s A sigma tau:
  TY Delta1;Gamma1 |- s : A ->
  (forall x B, atnd Delta1 x B -> SUB Delta2 |- sigma x <: B.[sigma] ) ->
  (forall x B, atn Gamma1 x B -> TY Delta2;Gamma2 |- tau x : B.[sigma]) ->
  TY Delta2;Gamma2 |- s.|[sigma].[tau] : A.[sigma].
Proof.
  intros H.
  autorevert H. induction H; intros; asimpl.
  - now eauto.
  - econstructor.
    + apply IHty; eauto.
      intros ? ? H_get. destruct x; asimpl in *; subst;
      eauto using ty_weak_ter1. now constructor.
    + eauto using wf_subst, sub_wf_1.
  - econstructor; eauto.
  - econstructor. apply IHty.
    + intros ? ? H_get. inv H_get; asimpl.
      * econstructor. constructor; eauto.
        asimpl. apply sub_refl. eauto using wf_weak1, wf_subst, sub_wf_1.
      * eapply sub_weak; eauto using @atnd. now autosubst.
    + intros.
      apply mmap_atn in H3. ainv.
      eapply ty_weak_ty'; eauto. now autosubst.
    + eauto using wf_subst, sub_wf_1.
  - subst. simpl in *. econstructor; eauto using sub_subst. now autosubst.
  - eauto using ty, sub_subst.
Qed.

Corollary ty_subst_term Delta Gamma1 Gamma2 s A sigma:
  TY Delta;Gamma1 |- s : A ->
  (forall x B, atnd Delta x B -> wf_ty Delta B) ->
  (forall x B, atn Gamma1 x B -> TY Delta;Gamma2 |- sigma x : B) ->
  TY Delta;Gamma2 |- s.[sigma] : A.
Proof.
  intros.
  cutrewrite(s = s.|[ids]);[idtac|autosubst].
  cutrewrite (A = A.[ids]);[idtac|autosubst].
  eapply ty_subst; eauto; intros; asimpl; eauto using sub, sub_refl.
Qed.

Lemma can_form_arr {s A B}:
  TY nil;nil |- s : Arr A B -> value s -> exists C t, s = Abs C t.
Proof.
  intros H.
  depind H; intros; eauto; ainv.
  inv H0. ainv. eauto.
Qed.

Lemma can_form_all {s A B}:
  TY nil;nil |- s : All A B -> value s -> exists C t, s = TAbs C t.
Proof.
  intros H.
  depind H; intros; eauto; ainv.
  inv H0. ainv. eauto.
Qed.

Theorem ev_progress s A:
  TY nil;nil |- s : A -> value s \/ exists t,  EV s => t.
Proof.
  intros. depind H.
  - inv H.
  - left; constructor.
  - right. destruct IHty1 as [? | [? ?]].
    + edestruct (can_form_arr H H1) as [? [? ?]]; subst. eauto using eval.
    + eauto using eval.
  - left; constructor.
  - right. destruct IHty as [? | [? ?]].
    + edestruct (can_form_all H H1) as [? [? ?]]; subst. eauto using eval.
    + eauto using eval.
  - assumption.
Qed.

Lemma ty_inv_abs {Delta Gamma A A' B C s}:
  TY Delta;Gamma |- Abs A s : C   ->   SUB Delta |- C <: Arr A' B   ->
  (SUB Delta |- A' <: A /\
    exists B', TY Delta;A::Gamma |- s : B' /\ SUB Delta |- B' <: B).
Proof.
  intros H. depind H; intros.
  - inv H1. split; eauto.
  - eauto using sub_trans.
Qed.

Lemma ty_inv_tabs {Delta Gamma A A' B C s}:
  TY Delta;Gamma |- TAbs A s : C   ->   SUB Delta |- C <: All A' B   ->
  (SUB Delta |- A' <: A /\ exists B',
   TY A'::Delta;Gamma..[ren(+1)] |- s : B' /\ SUB A'::Delta |- B' <: B).
Proof.
  intros H. depind H; intros.
  - inv H1. split; eauto.
    eexists. split; eauto. eapply (ty_narrow nil); eauto.
  - eauto using sub_trans.
Qed.

Theorem preservation Delta Gamma s t A :
  TY Delta;Gamma |- s : A -> EV s => t ->
  (forall x B, atnd Delta x B -> wf_ty Delta B) ->
  TY Delta;Gamma |- t : A.
Proof.
  intros H_ty H_ev.
  autorevert H_ev. induction H_ev; intros; depind H_ty; eauto using ty.
  - inv H_ty1.
    + eapply ty_subst_term; eauto. intros [|] ? ?; simpl in *;
      subst; eauto using ty.
    + pose proof (ty_inv_abs H0 H1) as [? [B' [? ?]]].
      eapply ty_subst_term; eauto using ty.
      intros [|] ? ?; simpl in *; subst; eauto using ty.
  - cutrewrite (s.|[B/] = s.|[B/].[ids]);[idtac|autosubst].
    inv H_ty; [idtac | pose proof (ty_inv_tabs H1 H2) as [? [B' [? ?]]]];
    (eapply ty_subst; eauto using ty; [
        now intros ? ? H_atnd; inv H_atnd; asimpl; eauto using sub, sub_refl
      | now intros [|] ? H_atn; simpl in *; subst; apply mmap_atn in H_atn;
        destruct H_atn as [? [? ?]]; subst; asimpl; eauto using ty ]).
Qed.

(* Local Variables: *)
(* coq-load-path: (("." "Plain")) *)
(* End: *)
