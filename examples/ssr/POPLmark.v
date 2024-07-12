(** * POPLmark Part 1a + 2a

    The #<a href="http://www.seas.upenn.edu/~plclub/poplmark/">POPLmark</a>#
    challenge is a set of benchmark problems to evaluate approaches to the
    formalization of syntactic theories. We solve parts 1a and 2a, that is,
    progress and preservation of System F with subtyping.

    The formalization in this file does not follow the paper proofs as closely,
    and in particular does not contain well-formedness assumptions.
 *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import AutosubstSsr Context.

(** **** Syntax *)

Inductive type : Type :=
| TyVar (x : var)
| Top
| Arr (A1 A2 : type)
| All (A1 : type) (A2 : {bind type}).

Inductive term :=
| TeVar (x : var)
| Abs (A : type) (s : {bind term})
| App (s t : term)
| TAbs (A : type) (s : {bind type in term})
| TApp (s : term) (A : type).

(** **** Substitutions *)

Global Instance Ids_type : Ids type. derive. Defined.
Global Instance Rename_type : Rename type. derive. Defined.
Global Instance Subst_type : Subst type. derive. Defined.
Global Instance SubstLemmas_type : SubstLemmas type. derive. Qed.
Global Instance HSubst_term : HSubst type term. derive. Defined.
Global Instance Ids_term : Ids term. derive. Defined.
Global Instance Rename_term : Rename term. derive. Defined.
Global Instance Subst_term : Subst term. derive. Defined.
Global Instance HSubstLemmas_term : HSubstLemmas type term. derive. Qed.
Global Instance SubstHSubstComp_type_term : SubstHSubstComp type term. derive. Qed.
Global Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

(** **** Subtyping *)

Notation "Gamma `_ x" := (dget Gamma x) (at level 2).
Notation "Gamma ``_ x" := (get Gamma x) (at level 3, x at level 2,
  left associativity, format "Gamma ``_ x").

Reserved Notation "'SUB' Gamma |- A <: B"
  (at level 68, A at level 99, no associativity).
Inductive sub (Gamma : list type) : type -> type -> Prop :=
| sub_top A :
    SUB Gamma |- A <: Top
| sub_var_refl x :
    SUB Gamma |- TyVar x <: TyVar x
| sub_var_trans x A :
    x < size Gamma -> SUB Gamma |- Gamma`_x <: A -> SUB Gamma |- TyVar x <: A
| sub_fun A1 A2 B1 B2 :
    SUB Gamma |- B1 <: A1 -> SUB Gamma |- A2 <: B2 ->
    SUB Gamma |- Arr A1 A2 <: Arr B1 B2
| sub_all A1 A2 B1 B2 :
    SUB Gamma |- B1 <: A1 -> SUB (B1 :: Gamma) |- A2 <: B2 ->
    SUB Gamma |- All A1 A2 <: All B1 B2
where "'SUB' Gamma |- A <: B" := (sub Gamma A B).

Lemma sub_refl Gamma A : SUB Gamma |- A <: A.
Proof. elim: A Gamma; eauto using sub. Qed.
Global Hint Resolve sub_refl : core.

Lemma sub_ren Gamma Delta xi A B :
  (forall x, x < size Gamma -> xi x < size Delta) ->
  (forall x, x < size Gamma -> Delta`_(xi x) = (Gamma`_x).[ren xi]) ->
  SUB Gamma |- A <: B -> SUB Delta |- A.[ren xi] <: B.[ren xi].
Proof.
  move=> sub eqn ty. elim: ty Delta xi sub eqn => {A B} Gamma //=;
    eauto using sub.
  - move=> x A lt _ ih Delta xi sub eqn. apply: sub_var_trans. exact: sub.
    rewrite eqn //. exact: ih.
  - move=> A1 A2 B1 B2 _ ih1 _ ih2 Delta xi sub eqn. apply: sub_all.
    exact: ih1. asimpl. apply: ih2. by move=> [|x /sub].
    move=> [_|x /eqn/=->]; autosubst.
Qed.

Lemma sub_weak Gamma A B C :
  SUB Gamma |- A <: B -> SUB (C :: Gamma) |- A.[ren (+1)] <: B.[ren (+1)].
Proof. exact: sub_ren. Qed.

Definition transitivity_at (B : type) := forall Gamma A C xi,
  SUB Gamma |- A <: B.[ren xi] -> SUB Gamma |- B.[ren xi] <: C ->
  SUB Gamma |- A <: C.

Lemma transitivity_proj Gamma A B C :
  transitivity_at B ->
  SUB Gamma |- A <: B -> SUB Gamma |- B <: C -> SUB Gamma |- A <: C.
Proof. move=> /(_ Gamma A C id). autosubst. Qed.
Global Hint Resolve transitivity_proj : core.

Lemma transitivity_ren B xi : transitivity_at B -> transitivity_at B.[ren xi].
Proof. move=> h Gamma A C zeta. asimpl. exact: h. Qed.

Lemma sub_narrow_t Gamma Delta A B :
  (forall x, x < size Gamma -> x < size Delta) ->
  (forall x, x < size Gamma -> SUB Delta |- Delta`_x <: Gamma`_x) ->
  (forall x, x < size Gamma ->
    Delta`_x = Gamma`_x \/ transitivity_at (Gamma`_x)) ->
  SUB Gamma |- A <: B -> SUB Delta |- A <: B.
Proof with eauto using sub.
  move=> h1 h2 h3 ty. elim: ty Delta h1 h2 h3 => {Gamma A B} /=...
  - move=> Gamma x A lt _ ih Delta h1 h2 h3. apply: sub_var_trans...
    case: (h3 x lt) => [->|]...
  - move=> Gamma A1 A2 B1 B2 _ ih1 _ ih2 Delta h1 h2 h3. apply: sub_all...
    apply: ih2 => [[|x /h1]|[|x /h2/sub_weak]|[_|x /h3[|]]] //=...
    move=>->... move=> tr. right. exact: transitivity_ren.
Qed.

Definition is_var (A : type) : bool := if A is TyVar _ then true else false.

Lemma sub_trans_snoc Gamma B C :
  (forall A, ~~is_var A ->
    SUB Gamma |- A <: B -> SUB Gamma |- B <: C -> SUB Gamma |- A <: C) ->
  forall A, SUB Gamma |- A <: B -> SUB Gamma |- B <: C -> SUB Gamma |- A <: C.
Proof with eauto using sub.
  move=> h A ty. elim: ty C h =>{Gamma A B}... move=> Gamma A C h1 h2. inv h2...
Qed.

Lemma sub_trans_t B : transitivity_at B.
Proof with eauto using sub.
  elim: B => [x||B1 ih1 B2 ih2|B1 ih1 B2 ih2] Gamma A C xi; asimpl...
  - apply: sub_trans_snoc A => A e ty. by inv ty.
  - move=> t1 t2. inv t2...
  - apply: sub_trans_snoc A => A e ty1 ty2. inv ty1 => //. inv ty2...
  - apply: sub_trans_snoc A => A e ty1 ty2. inv ty1 => //. inv ty2...
    apply: sub_all... eapply ih2... move: H3. apply: sub_narrow_t...
    + case=> //= _. exact: sub_weak.
    + move=> [|x] _... right => /=. asimpl. exact: transitivity_ren.
Qed.

Corollary sub_trans Gamma A B C :
  SUB Gamma |- A <: B -> SUB Gamma |- B <: C -> SUB Gamma |- A <: C.
Proof. move: (sub_trans_t B); eauto. Qed.

Corollary sub_narrow Gamma A B C1 C2 :
  SUB Gamma |- C1 <: C2 -> SUB C2 :: Gamma |- A <: B ->
  SUB C1 :: Gamma |- A <: B.
Proof.
  move=> ty. apply: sub_narrow_t => //.
  - case=> //= _. exact: sub_weak.
  - move=> [_/=|x]; eauto. right. apply: transitivity_ren. exact: sub_trans_t.
Qed.

Lemma sub_subst Gamma Delta A B sigma :
  (forall x, x < size Gamma -> SUB Delta |- sigma x <: (Gamma`_x).[sigma]) ->
  SUB Gamma |- A <: B -> SUB Delta |- A.[sigma] <: B.[sigma].
Proof with eauto using sub.
  move=> h ty. elim: ty Delta sigma h => {A B} Gamma...
  - move=> x A lt _ ih Delta sigma h /=. apply: sub_trans (h _ lt) _. exact: ih.
  - move=> A1 A2 B1 B2 _ ih1 _ ih2 Delta sigma h /=. apply: sub_all...
    apply: ih2 => -[_|x /h/sub_weak]. apply: sub_var_trans => //. autosubst.
    autosubst.
Qed.

(** **** Typing *)

Reserved Notation "'TY' Delta ; Gamma |- A : B"
  (at level 68, A at level 99, no associativity,
   format "'TY'  Delta ; Gamma  |-  A  :  B").
Inductive ty (Delta Gamma : list type) : term -> type -> Prop :=
| ty_var x :
    x < size Gamma ->
    TY Delta;Gamma |- TeVar x : Gamma``_x
| ty_abs A B s :
    TY Delta;A::Gamma |- s : B ->
    TY Delta;Gamma |- Abs A s : Arr A B
| ty_app A B s t:
    TY Delta;Gamma |- s : Arr A B -> TY Delta;Gamma |- t : A ->
    TY Delta;Gamma |- App s t : B
| ty_tabs A B s :
    TY A::Delta;Gamma..[ren (+1)] |- s : B ->
    TY Delta;Gamma |- TAbs A s : All A B
| ty_tapp A B C s :
    TY Delta;Gamma |- s : All A B -> SUB Delta |- C <: A ->
    TY Delta;Gamma |- TApp s C : B.[C/]
| ty_sub A B s :
    TY Delta;Gamma |- s : A -> SUB Delta |- A <: B ->
    TY Delta;Gamma |- s : B
where "'TY' Delta ; Gamma |- s : A" := (ty Delta Gamma s A).

Definition value (s : term) : bool :=
  match s with Abs _ _ | TAbs _ _ => true | _ => false end.

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

Lemma ty_evar Delta Gamma x A :
  A = Gamma``_x -> x < size Gamma -> TY Delta;Gamma |- TeVar x : A.
Proof. move->. exact: ty_var. Qed.

Lemma ty_etapp Delta Gamma A B C D s :
  D = B.[C/] ->
  TY Delta;Gamma |- s : All A B -> SUB Delta |- C <: A ->
  TY Delta;Gamma |- TApp s C : D.
Proof. move->. exact: ty_tapp. Qed.

(** **** Preservation *)

Lemma ty_ren Delta Gamma1 Gamma2 s A xi :
  (forall x, x < size Gamma1 -> xi x < size Gamma2) ->
  (forall x, x < size Gamma1 -> Gamma2``_(xi x) = Gamma1``_x) ->
  TY Delta;Gamma1 |- s : A -> TY Delta;Gamma2 |- s.[ren xi] : A.
Proof with eauto using ty.
  move=> h1 h2 ty. elim: ty Gamma2 xi h1 h2 => {Delta Gamma1 s A} /=...
  - move=> Delta Gamma1 x lt Gamma2 xi h1 h2. rewrite -h2 //. apply: ty_var...
  - move=> Delta Gamma1 A B s _ ih Gamma2 xi h1 h2. asimpl. apply: ty_abs.
    by apply: ih => [[|x/h1]|[|x/h2]].
  - move=> Delta Gamma1 A B s _ ih Gamma2 xi h1 h2. apply: ty_tabs.
    apply: ih => x. by rewrite !size_map => /h1. rewrite !size_map => lt.
    rewrite !get_map ?h2 //. exact: h1.
Qed.

Lemma ty_weak Delta Gamma s A B :
  TY Delta;Gamma |- s : A -> TY Delta; B :: Gamma |- s.[ren (+1)] : A.
Proof. exact: ty_ren. Qed.

Lemma ty_hsubst Delta1 Delta2 Gamma s A sigma :
  (forall x, x < size Delta1 -> SUB Delta2 |- sigma x <: (Delta1`_x).[sigma]) ->
  TY Delta1;Gamma |- s : A -> TY Delta2;Gamma..[sigma] |- s.|[sigma] :A.[sigma].
Proof with eauto using ty.
  move=> h ty. elim: ty Delta2 sigma h => {Delta1 Gamma s A}/=...
  - move=> Delta1 Gamma x lt Delta2 sigma h. apply: ty_evar. by rewrite get_map.
    by rewrite size_map.
  - move=> Delta1 Gamma A B s _ ih Delta2 sigma h. apply: ty_tabs.
    specialize (ih (A.[sigma] :: Delta2) (up sigma)). move: ih. asimpl.
    apply. move=> [_|x/h/sub_weak] /=. apply: sub_var_trans => //. autosubst.
    autosubst.
  - move=> Delta1 Gamma A B C s _ ih sub Delta2 sigma h. asimpl.
    eapply ty_etapp. 2: { by eapply ih. } autosubst. exact: sub_subst sub.
  - move=> Delta1 Gamma A B s _ ih sub Delta2 sigma h.
    eapply ty_sub. by eapply ih. exact: sub_subst sub.
Qed.

Lemma ty_tweak Delta Gamma s A B :
  TY Delta;Gamma |- s : A ->
  TY B :: Delta; Gamma..[ren (+1)] |- s.|[ren (+1)] : A.[ren (+1)].
Proof. apply: ty_hsubst => x /= lt. exact: sub_var_trans. Qed.

Lemma ty_subst Delta Gamma1 Gamma2 s A sigma :
  (forall x, x < size Gamma1 -> TY Delta;Gamma2 |- sigma x : Gamma1``_x) ->
  TY Delta;Gamma1 |- s : A -> TY Delta;Gamma2 |- s.[sigma] : A.
Proof with eauto using ty.
  move=> h ty. elim: ty Gamma2 sigma h => {Delta Gamma1 s A}/=...
  - move=> Delta Gamma1 A B s _ ih Gamma2 sigma h /=. apply: ty_abs.
    apply: ih. move=> [_|x/h/ty_weak]... autosubst.
  - move=> Delta Gamma1 A B s _ ih Gamma2 sigma h. apply: ty_tabs. apply: ih.
    move=> x. rewrite size_map => lt. rewrite get_map //=. exact/ty_tweak/h.
Qed.

Lemma ty_narrow Delta Gamma s A B1 B2 :
  TY Delta;B2::Gamma |- s : A -> SUB Delta |- B1 <: B2 ->
  TY Delta;B1::Gamma |- s : A.
Proof.
  move=> ty sub. rewrite -[s]subst_id. apply: ty_subst ty => -[_/=|x lt];
    [apply: ty_sub sub|]; exact: ty_var.
Qed.

Lemma ty_beta Delta Gamma s t A B :
  TY Delta;Gamma |- t : A -> TY Delta;A::Gamma |- s : B ->
  TY Delta;Gamma |- s.[t/] : B.
Proof.
  move=> ty. apply: ty_subst => -[|n lt] //=. exact: ty_var.
Qed.

Lemma ty_narrowT Delta Gamma s A B1 B2 :
  TY B2::Delta;Gamma |- s : A -> SUB Delta |- B1 <: B2 ->
  TY B1::Delta;Gamma |- s : A.
Proof.
  move=> ty sub. cut (TY B1::Delta;Gamma..[ids] |- s.|[ids] : A.[ids]).
  autosubst. apply: ty_hsubst ty => -[_|x lt]; asimpl.
  apply: sub_var_trans => //=. exact: sub_weak. exact: sub_var_trans.
Qed.

Lemma ty_betaT Delta Gamma s A B C :
  SUB Delta |- C <: A -> TY A :: Delta;Gamma..[ren (+1)] |- s : B ->
  TY Delta;Gamma |- s.|[C/] : B.[C/].
Proof.
  move=> subt ty.
  cut (TY Delta;Gamma..[ren(+1)]..[C/] |- s.|[C/] : B.[C/]). autosubst.
  apply: ty_hsubst ty => -[_|x lt]; asimpl => //. exact: sub_var_trans.
Qed.

Lemma ty_inv_abs' Delta Gamma A A' B T s :
  TY Delta;Gamma |- Abs A s : T -> SUB Delta |- T <: Arr A' B ->
  TY Delta;A'::Gamma |- s : B.
Proof.
  move e:(Abs A s) => t ty. elim: ty A A' B s e => {Delta Gamma t T} //.
  - move=> Delta Gamma A B s h _ A' A'' B' s' [e1 e2]. subst => sub. inv sub.
    apply: ty_narrow H2. exact: ty_sub h _.
  - move=> Delta Gamma A B s _ ih sub1 A' A'' B' s' eqn sub2. apply: ih eqn _.
    eapply (sub_trans _ _ _ _ sub1 sub2).
Qed.

Lemma ty_inv_abs Delta Gamma A A' B s :
  TY Delta;Gamma |- Abs A s : Arr A' B -> TY Delta;A'::Gamma |- s : B.
Proof. move=> ty. apply: ty_inv_abs' ty _. eapply sub_refl. Qed.

Lemma ty_inv_tabs' Delta Gamma A A' B T s :
  TY Delta;Gamma |- TAbs A s : T -> SUB Delta |- T <: All A' B ->
  TY A'::Delta;Gamma..[ren(+1)] |- s : B.
Proof.
  move e:(TAbs A s) => t ty. elim: ty A A' B s e => {Delta Gamma t T} //.
  - move=> Delta Gamma  A B s ty _ A' A'' B' s' [e1 e2] sub. subst. inv sub.
    apply: ty_sub H4. exact: ty_narrowT ty _.
  - move=> Delta Gamma A B s _ ih sub1 A' A'' B' s' e sub2. apply: ih e _.
    exact: sub_trans sub1 sub2.
Qed.

Lemma ty_inv_tabs Delta Gamma A A' B s :
  TY Delta;Gamma |- TAbs A s : All A' B ->
  TY A'::Delta;Gamma..[ren(+1)] |- s : B.
Proof. move=> ty. exact: ty_inv_tabs' ty _. Qed.

Theorem preservation Delta Gamma s t A :
  TY Delta;Gamma |- s : A -> EV s => t -> TY Delta;Gamma |- t : A.
Proof with eauto using ty.
  move=> ty. elim: ty t => {Delta Gamma s A}...
  - move=> Delta Gamma x _ t ev. by inv ev.
  - move=> Delta Gamma A B s _ i t ev. by inv ev.
  - move=> Delta Gamma A B s t ty1 ih1 ty2 ih2 u ev. inv ev...
    move: ty1 => /ty_inv_abs. exact: ty_beta.
  - move=> Delta Gamma A B s _ _ t ev. by inv ev.
  - move=> Delta Gamma A B C s ty ih sub t ev. inv ev.
    + move: ty => /ty_inv_tabs. exact: ty_betaT.
    + apply: ty_tapp sub. exact: ih.
Qed.

(** **** Progress *)

Definition is_abs s := if s is Abs _ _ then true else false.
Definition is_tabs s := if s is TAbs _ _ then true else false.

Lemma canonical_arr' Delta Gamma s T A B :
  TY Delta;Gamma |- s : T -> SUB Delta |- T <: Arr A B -> value s -> is_abs s.
Proof.
  move=> ty. elim: ty A B => //= {Gamma s T} Delta Gamma A B s.
  - move=> ty _ A' B' sub. by inv sub.
  - move=> _ ih /sub_trans h A' B' /h. exact: ih.
Qed.

Lemma canonical_arr Delta Gamma s A B :
  TY Delta;Gamma |- s : Arr A B -> value s -> is_abs s.
Proof.
  move=> ty. apply: canonical_arr' ty (sub_refl _ _).
Qed.

Lemma canonical_all' Delta Gamma s T A B :
  TY Delta;Gamma |- s : T -> SUB Delta |- T <: All A B -> value s -> is_tabs s.
Proof.
  move=> ty. elim: ty A B => //= {Gamma s T} Delta Gamma A B s.
  - move=> _ _ A' B' sub. by inv sub.
  - move=> _ ih /sub_trans h A' B' /h. exact: ih.
Qed.

Lemma canonical_all Delta Gamma s A B :
  TY Delta;Gamma |- s : All A B -> value s -> is_tabs s.
Proof.
  move=> ty. apply: canonical_all' ty (sub_refl _ _).
Qed.

Lemma ev_progress' Delta Gamma s A :
  TY Delta;Gamma |- s : A -> Gamma = [::] -> value s \/ exists t, EV s => t.
Proof with eauto using eval.
  elim=> {Delta Gamma s A} /=; try solve [intuition].
  - move=> _ Gamma x lt eqn. by subst.
  - move=> Delta Gamma A B s t ty1 ih1 _ ih2 eqn. right.
    case: (ih1 eqn) => {ih1} [vs|[s' h1]]...
    case: (ih2 eqn) => {ih2 eqn} [vt|[t' h2]]...
    case: s {ty1 vs} (canonical_arr _ _ _ _ _ ty1 vs) => //...
  - move=> Delta Gamma A B C s ty ih sub eqn. right.
    case: (ih eqn) => {ih eqn}[vs|[s' h]]...
    case: s {ty vs} (canonical_all _ _ _ _ _ ty vs) => //...
Qed.

Theorem ev_progress s A:
  TY nil;nil |- s : A -> value s \/ exists t,  EV s => t.
Proof. move=> ty. exact: ev_progress' ty _. Qed.

(* Local Variables: *)
(* coq-load-path: (("." "Ssr") ("../../theories" "Autosubst")) *)
(* End: *)
