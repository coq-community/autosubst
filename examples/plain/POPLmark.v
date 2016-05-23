(** * POPLmark Part 1

    The #<a href="http://www.seas.upenn.edu/~plclub/poplmark/">POPLmark</a>#
    challenge is a set of benchmark problems to evaluate approaches to the
    formalization of syntactic theories.  We solve part 1, that is,
    progress and preservation of System F with subtyping.  *)

Require Import Program.Equality List.
Require Import Autosubst Autosubst.Size.
Require Import Autosubst.Morphisms.


Notation Typ := Sort1_2.
Notation Ter := Sort2_2.

Reserved Notation "'type'".
Reserved Notation "'term'".
Inductive constr : sort2 -> Type :=
| Var {o : sort2} (x : var) : constr o
| Top : type
| Arr (A1 A2 : type) : type
| All (A1 : type) (A2 : {bind Typ in type}) : type
| Abs (A : type) (s : {bind Ter in term}) : term
| App (s t : term) : term
| TAbs (A : type) (s : {bind Typ in term}) : term
| TApp (s : term) (A : type) : term
where "'type'" := (constr Typ) and "'term'" := (constr Ter).

Instance VarConstr_constr : VarConstr constr := @Var.
Instance Rename_constr : Rename constr. derive. Show Proof. Defined.
Instance Subst_constr : Subst constr. derive. Show Proof. Defined.
Instance SubstLemmas_constr : SubstLemmas constr. Admitted.

Instance size_constr o : Size (constr o).
assert(Size var) by exact(fun _ => 0). derive. Show Proof.
Defined.

Lemma ren_size_inv o (s : constr o) : forall xi zeta, size s.|[ren Typ xi, ren Ter zeta] = size s.
Proof.
  induction s; intros; sizesimpl; repeat(asimpl; autorew); try somega.
  now destruct o.
Qed.

Inductive wf_ty (Delta : var -> Prop) : type -> Prop :=
  | WfTy_Var x : Delta x -> wf_ty Delta (Var x)
  | WfTy_Top : wf_ty Delta Top
  | WfTy_Arr A B : wf_ty Delta A -> wf_ty Delta B -> wf_ty Delta (Arr A B)
  | WfTy_All A B : wf_ty Delta A -> wf_ty (True .: Delta) B -> wf_ty Delta (All A B)
.

Lemma wf_mono Delta Delta' A :
  wf_ty Delta A -> Delta <1= Delta' -> wf_ty Delta' A.
Proof.
  intros H; revert Delta'. induction H; intros Delta' HS; econstructor; eauto.
  apply IHwf_ty2. intros [|x]; trivial; simpl; apply HS.
Qed.

Lemma wf_weak Delta A xi : wf_ty (xi >> Delta) A -> wf_ty Delta A.[ren Typ xi].
Proof.
  autorevert A. depind A; intros; ainv; simpl in *; asimpl; eauto using wf_ty.
  constructor; asimpl; eauto. apply IHA0. now asimpl.
Qed.

(* not sure if this is the right version ... as there is no tau post composed onto the Delta ...*)
Lemma wf_subst Delta Delta' A (tau : var -> type) :
  wf_ty Delta A ->
  Delta <1= tau >> (wf_ty Delta') ->
  (* (forall x B, atnd Delta x B -> wf_ty Delta' (sigma x)) -> *)
  wf_ty Delta' A.[tau].
Proof.
  intros H. revert Delta' tau. induction H; intros Delta' tau HD.
  - asimpl. now apply HD.
  - constructor.
  - constructor; asimpl; auto.
  - constructor; asimpl; auto.
    apply IHwf_ty2. asimpl. intros [|]; simpl; intros.
    + constructor. now asimpl.
    + asimpl. apply wf_weak. asimpl. now apply HD.
Qed.

Notation "$?" := ltac:(eauto; econstructor; try econstructor; now eauto) (only parsing).

Reserved Notation "'SUB' Delta |- A <: B"
  (at level 68, A at level 99, no associativity).
Inductive sub (Delta : var -> type -> Prop) : type -> type -> Prop :=
| SA_Top A :
    wf_ty (DOM Delta) A -> SUB Delta |- A <: Top
| SA_Refl x :
    wf_ty (DOM Delta) (Var x) -> SUB Delta |- Var x <: Var x
| SA_Trans x A B :
    Delta x A -> SUB Delta |- A <: B -> SUB Delta |- Var x <: B
| SA_Arrow A1 A2 B1 B2 :
    SUB Delta |- B1 <: A1 -> SUB Delta |- A2 <: B2 ->
    SUB Delta |- Arr A1 A2 <: Arr B1 B2
| SA_All A1 A2 B1 B2 :
    SUB Delta |- B1 <: A1 -> wf_ty (DOM Delta) B1 -> SUB (((eq B1) .: Delta) >> rapp ((^(ren Typ (+1), ids)) >> eq)) |- A2 <: B2 ->
    SUB Delta |- All A1 A2 <: All B1 B2
where "'SUB' Delta |- A <: B" := (sub Delta A B).

Lemma sub_refl Delta A : wf_ty (DOM Delta) A -> SUB Delta |- A <: A.
Proof.
  revert Delta. dependent induction A; intros; ainv; constructor; eauto using wf_ty.
  - constructor. simpl; eauto.
  - apply IHA0. now asimpl.
Qed.

Lemma sub_weak (Delta Delta' : var -> type -> Prop) A1 A2 xi :
  SUB Delta |- A1 <: A2 ->
  Delta >> rapp (REL ^(ren Typ xi, ids)) <2= xi >> Delta' ->
  SUB Delta' |- A1.[ren Typ xi] <: A2.[ren Typ xi].
Proof.
  intros H. revert Delta' xi; induction H; intros Delta' xi HD.
  - constructor. apply wf_weak. eapply wf_mono; eauto.
    apply rsubset_subset in HD. revert HD. now asimpl.
  - apply sub_refl. apply wf_weak. eapply wf_mono; eauto.
    apply rsubset_subset in HD. revert HD. now asimpl.
  - eapply SA_Trans; eauto. apply HD. asimpl. exists A. now asimpl.
  - econstructor; eauto.
  - eapply SA_All; eauto.
    + asimpl. apply wf_weak. eapply wf_mono; eauto.
      apply rsubset_subset in HD. revert HD. now asimpl.
    + asimpl. apply IHsub2. asimpl. apply rsubset_scons; trivial using subset_refl.
      (* JK: this should not be necessary ... *)
      pose proof (rsubset_rcomp _ _ (REL ^ (ren Typ (+1), ids)) (REL ^ (ren Typ (+1), ids)) (HD) (rsubset_refl _)) as HD'.
      revert HD'. now asimpl.
Qed.

Lemma sub_mono Delta Delta' A B :
  SUB Delta |- A <: B -> Delta :< Delta' -> SUB Delta' |- A <: B.
Proof.
  intros. cut (SUB Delta' |- A.[ren Typ id] <: B.[ren Typ id]). autosubst. eapply sub_weak; eauto. autosubst.
Qed.

Corollary sub_trans Delta A B C:
  SUB Delta |- A <: B -> SUB Delta |- B <: C -> SUB Delta |- A <: C.
Admitted.
(* Proof. intros. eapply sub_trans'; eauto. Qed. *)

Lemma sub_subst (Delta Delta' : var -> type -> Prop) A1 A2 tau :
  SUB Delta |- A1 <: A2 ->
  Delta >> rapp (REL ^ (tau, ids)) <2= tau >> sub Delta'  ->
  DOM Delta <1= tau >> (wf_ty (DOM Delta')) -> (* can I get rid of this premise? *)
  SUB Delta' |- A1.[tau] <: A2.[tau].
Proof.
  intros H. revert Delta' tau; induction H; intros Delta' tau HDs HDw.
  - constructor. eapply wf_subst; eauto.
  - eapply sub_refl, wf_subst; eauto.
  - eapply sub_trans; eauto. apply HDs. asimpl. apply rapp_eq_app; auto.
  - constructor; eauto.
  - constructor; asimpl; eauto using wf_subst. (* apply IHsub2; asimpl. *)
    admit.
Admitted.

(* Lemma sub_weak1 Delta A A' B B' C : *)
(*   SUB Delta |- A <: B ->  A' = A.[ren(+1)] ->  B' = B.[ren(+1)] -> *)
(*   SUB (C :: Delta) |- A' <: B'. *)
(* Proof.  intros. eapply sub_weak; eauto using @atnd. Qed. *)

Lemma sub_wf {Delta A B} :
  SUB Delta |- A <: B -> wf_ty (DOM Delta) A /\ wf_ty (DOM Delta) B.
Proof.
  intros H. induction H; ainv; simpl; split; (try constructor); asimpl; eauto using wf_ty.
  - now asimpl in H2.
  - now asimpl in H3.
Qed.

(* Lemma sub_wf_1 Delta A B : SUB Delta |- A <: B -> wf_ty Delta A. *)
(* Proof. apply sub_wf. Qed. *)

(* Lemma sub_wf_2 Delta A B : SUB Delta |- A <: B -> wf_ty Delta B. *)
(* Proof. apply sub_wf. Qed. *)

Lemma conj' (A B : Prop) : A -> (A -> B) -> A /\ B.
Proof. tauto. Qed.

(* Lemma sub_trans' n : *)
(*   (forall Delta A B C, n = size B -> *)
(*      SUB Delta |- A <: B -> SUB Delta |- B <: C -> SUB Delta |- A <: C) /\ *)
(*   (forall Delta' Delta B B' A C, n = size B -> *)
(*      SUB Delta' ++ B :: Delta |- A <: C -> *)
(*      SUB Delta |- B' <: B -> *)
(*      SUB Delta' ++ B' :: Delta |- A <: C). *)
(* Proof. *)
(*   induction n as [n IH] using (size_rec (fun x => x)). *)
(*   apply conj'. *)
(*   { *)
(*     intros Delta A B C ? H_AB H_BC. subst. *)
(*     revert C H_BC. *)
(*     induction H_AB; intros; ainv; eauto using sub. *)
(*     - inv H_BC. *)
(*       + constructor. simpl. split; eauto using sub_wf_1, sub_wf_2. *)
(*       + constructor; eapply IH; eauto; somega. *)
(*     - inv H_BC. *)
(*       + constructor; constructor. *)
(*         * eapply sub_wf; now eauto. *)
(*         * eapply wf_weak'. now eapply (sub_wf H_AB2). now simpl. *)
(*       + rename B0 into C1. rename B3 into C2. *)
(*         constructor; eauto. *)
(*         * eapply IH; eauto; somega. *)
(*         * eapply IH; eauto; try somega. *)
(*           refine (proj2 (IH _ _) nil _ _ _ _ _ _ _ _); eauto; somega. *)
(*   } *)
(*   { *)
(*     intros H_trans Delta' Delta B B' A C ? H H_B'B. subst. *)
(*     revert B' H_B'B. *)
(*     depind H; intros; simpl in *. *)
(*     - constructor. *)
(*       eapply wf_weak'. eassumption. *)
(*       repeat rewrite app_length. simpl. omega. *)
(*     - constructor. simpl. *)
(*       apply atnd_defined. apply atnd_defined in H. *)
(*       repeat rewrite -> app_length in *. simpl in *. omega. *)
(*     - decide (x = length Delta'). *)
(*       + subst. *)
(*         econstructor. { apply atnd_repl. } *)
(*         apply atnd_steps' with (x := 0) in H. *)
(*         destruct H as [? [? H]]. inv H. *)
(*         eapply H_trans;[idtac | eapply sub_weak; *)
(*           try reflexivity; try eassumption | idtac]. *)
(*         * now rewrite ren_size_inv. *)
(*         * intros. change (B' :: Delta) with ((B' :: nil) ++ Delta). *)
(*           rewrite app_assoc. *)
(*           cutrewrite (S (length Delta') = length (Delta' ++ B' :: nil)). *)
(*           now apply atnd_steps. *)
(*           rewrite app_length. simpl. omega. *)
(*         * asimpl in IHsub. *)
(*           eapply IHsub; now eauto. *)
(*       + econstructor; eauto. *)
(*         eapply atnd_repl; now eauto. *)
(*     - constructor; now eauto. *)
(*     - constructor. *)
(*       + now eauto. *)
(*       + eapply wf_weak'. eassumption. *)
(*         repeat rewrite app_length. simpl. omega. *)
(*       + change (B1 :: Delta' ++ B' :: Delta) *)
(*           with ((B1 :: Delta') ++ B' :: Delta). *)
(*         eapply IHsub2; eauto. reflexivity. *)
(*   } *)
(* Qed. *)

(* Corollary sub_narrow Delta' Delta B B' A C : *)
(*      SUB Delta' ++ B :: Delta |- A <: C -> *)
(*      SUB Delta |- B' <: B -> *)
(*      SUB Delta' ++ B' :: Delta |- A <: C. *)
(* Proof. intros. eapply sub_trans'; eauto. Qed. *)

Inductive value : term -> Prop :=
| Value_Abs A s : value(Abs A s)
| Value_TAbs A s : value(TAbs A s).

Reserved Notation "'TY' Delta ; Gamma |- A : B"
  (at level 68, A at level 99, no associativity,
   format "'TY'  Delta ; Gamma  |-  A  :  B").
Inductive ty (Delta Gamma : var -> type -> Prop) : term -> type -> Prop :=
| T_Var A x :
    Gamma x A ->
    TY Delta;Gamma |- Var x : A
| T_Abs A B s:
    TY Delta; eq A .: Gamma |- s : B -> wf_ty (DOM Delta) A ->
    TY Delta;Gamma |- Abs A s : Arr A B
| T_App A B s t:
    TY Delta;Gamma |- s : Arr A B -> TY Delta;Gamma |- t : A ->
    TY Delta;Gamma |- App s t : B
| T_TAbs A B s :
    TY (eq A .: Delta) >> rapp (REL ^ (ren Typ (+1), ids)) ; Gamma >> rapp ( REL ^(ren Typ (+1), ids)) |- s : B -> wf_ty (DOM Delta) A ->
    TY Delta;Gamma |- TAbs A s : All A B
| T_TApp (A B : type) A' s B' :
    TY Delta;Gamma |- s : All A B ->
    SUB Delta |- A' <: A -> B' = B.[A' .: ids] ->
    TY Delta;Gamma |- TApp s A' : B'
| T_Sub A B s :
    TY Delta;Gamma |- s : A -> SUB Delta |- A <: B ->
    TY Delta;Gamma |- s : B
where "'TY' Delta ; Gamma |- s : A" := (ty Delta Gamma s A).

(* JK: same as with sub_mono, lots of automation potential *)
Lemma ty_mono Delta Gamma Delta' Gamma' s A :
  TY Delta;Gamma |- s : A -> Delta <2= Delta' -> Gamma <2= Gamma'-> TY Delta';Gamma' |- s : A.
Proof.
  intros H; revert Delta' Gamma'. induction H; intros Delta' Gamma' Hrs1 Hrs2.
  - constructor; eauto.
  - constructor.
    + apply IHty; auto using rsubset_scons, subset_refl.
    + eapply wf_mono; eauto using rsubset_subset.
  - econstructor; eauto.
  - constructor.
    + apply IHty; eauto using rsubset_rcomp, rsubset_scons, rsubset_refl, subset_refl.
    + eapply wf_mono; eauto using rsubset_subset.
  - econstructor; eauto using sub_mono.
  - econstructor; eauto using sub_mono.
Qed.

Reserved Notation "'EV' s => t"
  (at level 68, s at level 80, no associativity, format "'EV'   s  =>  t").
Inductive eval : term -> term -> Prop :=
| E_AppAbs A (s t : term) : EV App (Abs A s) t => s.[t .: ids]
| E_TAppTAbs A (s : term) B : EV TApp (TAbs A s) B => s.[B .: ids]
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

(* teach something like this to autosubst, without breaking internal nfs *)
Lemma subst_term_in_type (A : type) sigma tau : A.|[sigma, tau] = A.[sigma].
Proof. revert sigma tau. depind A; intros; asimpl; autorew; trivial. Qed.

(* note: we have to use the normalform A.|[sigma, ids] over A.[sigma],
   as the latter might break the calculation of normalforms. *)
Lemma subst_term_in_type' (A : type) sigma tau : A.|[sigma, tau] = A.|[sigma, ids].
Proof. revert sigma tau. depind A; intros; asimpl; autorew; trivial. Qed.
Hint Rewrite subst_term_in_type' : autosubst.

Definition upcons {o} (s : constr o) (Gamma : var -> constr o -> Prop) := ((eq s .: Gamma) >> rapp (REL (subst1 (ren o (+1))))).
Arguments upcons {o} s Gamma/ x _.


Lemma ctx_sub_ext (R1 R2 : var -> type -> Prop)  :
  R1 <2= R2 <->
  all (fun (T: Type) => forall (xi zeta : var -> var) tau sigma (S : type -> T -> Prop),
  R1 >> rapp (REL ^(ren Typ xi, ren Ter zeta)) >> rapp (REL ^(tau, sigma)) >> rapp S <2=
  R2 >> rapp (REL ^(ren Typ xi, ren Ter zeta)) >> rapp (REL ^(tau, sigma)) >> rapp S).
Proof.
  split; try firstorder.
  intros H. specialize (H type id id ids ids (@eq _)). asimplHQ H. trivial.
Qed.

(* JK: Testing asimplHQ *)

Example test_wf1 Delta A xi :
  (forall zeta, wf_ty Delta A.[ren Typ xi].[ren Typ zeta]) ->
  (forall zeta, wf_ty Delta A.[ren Typ (xi >> zeta)]).
Proof.
  intros H. asimplHQ H. exact H.
Qed.

Example test_wf2 Delta A :
  (forall (xi zeta : var -> var), wf_ty Delta A.[ren Typ xi].[ren Typ zeta]) ->
  (forall (xi zeta : var -> var), wf_ty Delta A.[ren Typ (xi >> zeta)]).
Proof.
  intros H. asimplHQ H. exact H.
Qed.

Example test_wf4 :
  (forall Delta A (xi zeta : var -> var), wf_ty Delta A.[ren Typ xi].[ren Typ zeta]) ->
  (forall Delta A (xi zeta : var -> var), wf_ty Delta A.[ren Typ (xi >> zeta)]).
Proof.
  intros H. asimplHQ H. exact H.
Qed.

Example test_rapp (A B : Type) (R : A -> B -> Prop) :
  (forall (C : Type) (S : B -> C -> Prop) (Q : A -> C -> Prop), (rapp R >> rapp S) <2= rapp Q) ->
  (forall (C : Type) (S : B -> C -> Prop) (Q : A -> C -> Prop), (rapp (R >> rapp S)) <2= rapp Q).
Proof.
  intros H. asimplHQ H. exact H.
Qed.

Lemma ty_weak' (Delta Delta' Gamma Gamma' : var -> type -> Prop) s A xi zeta :
  TY Delta;Gamma  |- s : A ->
  Delta >> rapp (REL ^(ren Typ xi, ids)) <2= xi >> Delta' ->
  Gamma >> rapp (REL ^(ren Typ xi, ids)) <2= zeta >> Gamma' ->
  TY Delta';Gamma' |- s.|[ren Typ xi, ren Ter zeta] : A.[ren Typ xi].
Proof.
  intros H. revert Delta' Gamma' xi zeta; induction H; intros Delta' Gamma' xi zeta HD HG.
  - constructor. apply HG. asimpl. now apply rapp_eq_app.
  - asimpl. eapply T_Abs.
    + eapply IHty; trivial. asimpl. apply rsubset_scons; trivial using subset_refl.
    + apply wf_weak. eapply wf_mono; eauto. apply rsubset_subset in HD. revert HD. now asimpl.
  - econstructor; eauto.
  - asimpl. eapply T_TAbs.
    + eapply IHty; asimpl.
      * apply rsubset_scons; trivial using subset_refl.
        (* we have to provide sufficiently many holes for unification: *)
        apply ctx_sub_ext; apply ctx_sub_ext in HD; unfold all in *.
        asimplHQ HD. intros. asimpl. trivial.
      * (* as above *) apply ctx_sub_ext; apply ctx_sub_ext in HG; unfold all in *.
        asimplHQ HG. intros. asimpl. trivial.
    + apply wf_weak. eapply wf_mono; eauto. apply rsubset_subset in HD. revert HD. now asimpl.
  - asimpl. econstructor; eauto; subst; asimpl; eauto using sub_weak.
  - econstructor; eauto using sub_weak.
Qed.

(* JK: Lib stuff *)
Lemma rsubset_fcomp {A B : Type} (f : A -> A) (R1 R2 : A -> B -> Prop) : R1 <2= R2 -> f >> R1 <2= f >> R2.
Proof. firstorder. Qed.

(* JK: not sure if this is the top-level form we want ... *)
Lemma ty_weak  xi zeta (Delta Gamma : var -> type -> Prop) s A :
  TY  xi >> Delta >> rapp (conv (REL ^(ren Typ xi, ids))); zeta >> Gamma >> rapp (conv (REL ^(ren Typ xi, ids))) |- s : A ->
  TY Delta;Gamma |- s.|[ren Typ xi, ren Ter zeta] : A.[ren Typ xi].
Proof.
  intros H. eapply ty_weak'; eauto; asimpl; apply rsubset_fcomp.
  - apply rsubset_trans with (R2:=Delta >> rapp eq).
    + apply rsubset_rcomp; eauto using rsubset_refl, preconv_K1, fun_func.
    + rewrite rapp_eq1. apply rsubset_refl.
  - apply rsubset_trans with (R2:= Gamma >> rapp eq).
    + apply rsubset_rcomp; eauto using rsubset_refl, preconv_K1, fun_func.
    + rewrite rapp_eq1. apply rsubset_refl.
Qed.

Lemma ty_subst' (Delta Delta' Gamma Gamma' : var -> type -> Prop) s A tau sigma :
  TY Delta;Gamma  |- s : A ->
  DOM Delta <1= tau >> (wf_ty (DOM Delta')) ->
  (* DOM Delta >> rapp (REL ^ (tau, ids)) <1= tau >> (wf_ty (DOM Delta')) -> *)
  Gamma >> rapp (REL ^ (tau, ids)) <2= sigma >> ty Delta' Gamma' ->
  TY Delta';Gamma' |- s.|[tau, sigma] : A.[tau].
Proof.
  intros H. revert Delta' Gamma' tau sigma; induction H; intros Delta' Gamma' tau sigma HD HG.
  - asimpl. apply HG. asimpl. now apply rapp_eq_app.
  - asimpl. eapply T_Abs.
    + admit. (* eapply IHty; trivial. asimpl. apply rsubset_scons; auto using subset_refl. *)
    + eapply wf_subst; eauto.
  - econstructor; eauto.
  - asimpl. eapply T_TAbs.
    + admit. (* eapply IHty; asimpl. *)
      (* * apply rsubset_scons. (* is there a reason why this requires a conjunct? *) *)
      (*   split; [apply subset_refl|]. *)
      (*   pose proof (rsubset_rcomp _ _ ((^ (ren Typ (+1), ids)) >> eq) ((^ (ren Typ (+1), ids)) >> eq) (HD) (rsubset_refl _)) as HD'. *)
      (*   revert HD'. now asimpl. (* asimpl should yield a goal where rsubset_rcomp can be applied directly ... *) *)
      (* * pose proof (rsubset_rcomp _ _ ((^ (ren Typ (+1), ids)) >> eq) ((^ (ren Typ (+1), ids)) >> eq) (HG) (rsubset_refl _)) as HG'. *)
      (*   revert HG'. now asimpl. (* asimpl should yield a goal where rsubset_rcomp can be applied directly ... *) *)
    + eapply wf_subst; eauto.
  - asimpl. econstructor; eauto; subst; asimpl. eauto using sub_weak.
  - econstructor; eauto. using sub_weak.
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
  apply ty_subst with (Delta1 := Delta) (Gamma1 := Gamma1); eauto; intros; asimpl; eauto using sub, sub_refl.
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
(* coq-load-path: (("." "Plain") ("../../theories" "Autosubst")) *)
(* End: *)
