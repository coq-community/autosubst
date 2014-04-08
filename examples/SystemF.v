Require Import Autosubst MMap.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Definitions *)

Inductive type : Type :=
| TyVar (x : var)
| Arr   (A B : type)
| All   (A : {bind type}).

Inductive term :=
| TeVar (x : var)
| Abs   (A : type) (s : {bind term})
| App   (s t : term)
| TAbs  (s : {in term bind type})
| TApp  (s : term) (A : type).

(* Substitution Lemmas *)

Instance VarConstr_type : VarConstr type. derive_VarConstr. Defined.
Instance Rename_type : Rename type. derive_Rename. Defined.
Instance Subst_type : Subst type. derive_Subst. Defined.

Instance substLemmas_type : SubstLemmas type. derive_SubstLemmas. Qed.

Instance hsubst_term : HSubst type term. derive_HSubst. Defined.

Instance VarConstr_term : VarConstr term. derive_VarConstr. Defined.
Instance Rename_term : Rename term. derive_Rename. Defined.
Instance Subst_term : Subst term. derive_Subst. Defined.

Instance HSubstLemmas_term : HSubstLemmas type term _ _ _ _. derive_HSubstLemmas. Qed.

Instance SubstHSubstComp_type_term : SubstHSubstComp type term _ _.
derive_SubstHSubstComp.
Qed.

Instance substLemmas_term : SubstLemmas term. derive_SubstLemmas. Qed.

(* Call-by value reduction *)

Inductive eval : term -> term -> Prop :=
| eval_beta (A : type) (s t u1 u2 v : term) :
    eval s (Abs A u1) -> eval t u2 -> eval (u1.[u2.:Var]) v -> eval (App s t) v
| eval_tbeta (B : type) (s A v : term) :
    eval s (TAbs A) -> eval (A.|[B.:Var]) v -> eval (TApp s B) v
| eval_abs (A : type) (s : term) :
    eval (Abs A s) (Abs A s)
| eval_tabs (A : term) :
    eval (TAbs A) (TAbs A).
Hint Resolve eval_abs eval_tabs.

(* Syntactic typing *)

Definition ctx := seq type.
Local Notation "Gamma `_ i" := (nth (Var 0) Gamma i).
Definition lift (Gamma : ctx) := [seq A.[ren (+1)] | A <- Gamma].

Inductive has_type (Gamma : ctx) : term -> type -> Prop :=
| ty_var (x : var) :
    x < size Gamma -> has_type Gamma (Var x) Gamma`_x
| ty_abs (A B : type) (s : term) :
    has_type (A :: Gamma) s B ->
    has_type Gamma (Abs A s) (Arr A B)
| ty_app (A B : type) (s t : term) :
    has_type Gamma s (Arr A B) ->
    has_type Gamma t A ->
    has_type Gamma (App s t) B
| ty_tabs (A : type) (s : term) :
    has_type (lift Gamma) s A ->
    has_type Gamma (TAbs s) (All A)
| ty_tapp (A B : type) (s : term) :
    has_type Gamma s (All A) ->
    has_type Gamma (TApp s B) A.[B.:Var].

(* Semantic typing *)

Definition L (P : term -> Prop) (s : term) :=
  exists2 v, eval s v & P v.

Fixpoint V (A : type) (rho : var -> term -> Prop) (v : term) {struct A} : Prop :=
  match A with
    | TyVar X => eval v v /\ rho X v
    | Arr A B => exists A' : type, exists2 s : term, v = Abs A' s &
        forall u, V A rho u -> L (V B rho) s.[u.:Var]
    | All A => exists2 s : term, v = TAbs s &
        forall i (B : type), L (V A (i .: rho)) s.|[B.:Var]
  end.
Notation E A rho := (L (V A rho)).

Lemma V_value A rho v : V A rho v -> eval v v.
Proof. by elim: A => [x[]|A _ B _/=[A'[s->]]|A _/=[s->]]. Qed.
Hint Resolve V_value.

Lemma V_to_E A rho v : V A rho v -> E A rho v.
Proof. exists v; eauto. Qed.
Hint Resolve V_to_E.

Lemma eq_V A rho1 rho2 v :
  (forall X v, eval v v -> (rho1 X v <-> rho2 X v)) -> V A rho1 v -> V A rho2 v.
Proof.
  elim: A rho1 rho2 v => //=.
  - move=> x rho1 rho2 v eqn [ev /eqn]. by intuition.
  - move=> A ih1 B ih2 rho1 rho2 v eqn [A' [s -> h]]. exists A'.
    exists s=>// u /ih1/h[]. by move=> X w; split; apply eqn.
    move=> w ev /ih2 ih. by exists w; eauto.
  - move=> A ih rho1 rho2 v eqn [s->h]. exists s => // P B.
    case: (h P B) => u ev /ih va. exists u => //. apply: va => -[|X] //=.
    exact: eqn.
Qed.

Lemma V_ren A rho s xi :
  V A.[ren xi] rho s <-> V A (xi >>> rho) s.
Proof.
  elim: A rho s xi => //=.
  - move=> A ih1 B ih2 rho v xi. split=> -[A' [s->h]]; do 2 eexists; try reflexivity;
      move=> t /ih1/h[u ev]/ih2 ih; by exists u.
  - move=> A ih rho s xi; autosubst.
    split=> -[s' -> h]; eexists; autosubst=> P B; move: {h} (h P B) => [v ev].
    + move=> /ih {ih} ih. exists v => //. by autosubst in ih.
    + move=> h. exists v => //. apply/ih. by autosubst.
Qed.

Lemma E_ren A rho s xi :
  E A.[ren xi] rho s <-> E A (xi >>> rho) s.
Proof.
  split=> -[v ev /V_ren h]; by exists v.
Qed.

Lemma V_subst A rho v sigma :
  V A.[sigma] rho v <-> V A (fun x => V (sigma x) rho) v.
Proof.
  elim: A rho v sigma.
  - move=> x rho v sigma /=. split; intuition eauto.
  - move=> A ih1 B ih2 rho v sigma /=. split=> -[A' [s->h]]; (do 2 eexists) => //;
      move=> t /ih1/h[u ev]/ih2 ih; by exists u.
  - move=> A ih rho v sigma. split; autosubst; move=> [s->{v}h]; eexists=> [//|P B].
    + move: (h P B) => [v ev /ih hv]. exists v => //. apply: eq_V hv => -[|X] //= u.
      by intuition. move=> _. exact: V_ren.
    + move: (h P B) => [v ev hv]. exists v => //. apply/ih. apply: eq_V hv => -[|X] //= u.
      intuition. split => [p|/V_ren//]. by apply/V_ren.
Qed.

Definition VG (Gamma : ctx) (rho : var -> term -> Prop) (sigma : var -> term) : Prop :=
  forall x, x < size Gamma -> E Gamma`_x rho (sigma x).

Theorem soundness Gamma s A :
  has_type Gamma s A -> forall delta sigma rho, VG Gamma rho sigma -> E A rho s.|[delta].[sigma].
Proof.
  elim=> {Gamma s A} [Gamma x xe|Gamma A B s _ ih|Gamma A B s t _ ih1 _ ih2|
                      Gamma A s _ ih|Gamma A B s _ ih] delta sigma rho l.
  - exact: l.
  - eexists; first by autosubst. (do 2 eexists)=> [//|t vt]. autosubst.
    apply: ih=> -[_/=|x/l//]. exact: V_to_E.
  - case: (ih1 delta _ _ l) => {ih1} /= v ev1 [A' [u eq ih1]]; subst v.
    case: (ih2 delta _ _ l) => {ih2} v ev2 ih2.
    case: (ih1 _ ih2) => {ih1} w ev3 ih1. exists w => //.
    exact: eval_beta ev1 ev2 ev3.
  - apply: V_to_E. eexists=> [//=|P B]. autosubst. apply: ih => x /=.
    rewrite size_map => wf. rewrite (nth_map (Var 0)) //. apply/E_ren. exact: l.
  - move: (ih delta _ _ l) => [v ev1 {ih} /=[s' eq ih]]; subst v.
    specialize (ih (V B rho) B.[delta]). move: ih => [v ev2 ih]. exists v.
    exact: eval_tbeta ev1 ev2. apply/V_subst. apply: eq_V ih => -[|x] //=.
    by intuition.
Qed.

Corollary soundness_nil s A :
  has_type [::] s A -> E A (fun _ _ => False) s.
Proof.
  move=> /soundness h. specialize (h Var Var (fun _ _ => False)). autosubst in h.
  apply: h. by [].
Qed.

Corollary normalization s A :
  has_type [::] s A -> exists v, eval s v.
Proof.
  move=> /soundness_nil[v hv] _. by exists v.
Qed.

Corollary consistency s :
  ~has_type [::] s (All (Var 0)).
Proof.
  move=> /soundness_nil[v _ /= [t {s v} _ /(_ (fun _ => False) (TyVar 0))]].
  by move=> [s {t} _ []].
Qed.

Inductive step : term -> term -> Prop :=
| step_beta (A : type) (s s' t : term) : s' = s.[t.:Var] -> step (App (Abs A s) t) (s')
| step_tbeta (B : type) s s' : s' = s.|[B.:Var] -> step (TApp (TAbs s) B) s'
| step_app1 s s' t : step s s' -> step (App s t) (App s' t)
| step_app2 s t t' : step t t' -> step (App s t) (App s t')
| step_abs (A : type) (s t: term) : step s t ->
    step (Abs A s) (Abs A t).

Lemma substitutivity s t : step s t -> forall sigma tau, step s.|[tau].[sigma] t.|[tau].[sigma].
Proof. elim=> /=; constructor; subst; autosubst. Qed.