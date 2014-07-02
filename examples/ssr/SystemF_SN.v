Require Import Autosubst.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** **** Definitions *)

Inductive type : Type :=
| TyVar (x : var)
| Arr   (A B : type)
| All   (A : {bind type}).

Inductive term :=
| TeVar (x : var)
| Abs   (A : type) (s : {bind term})
| App   (s t : term)
| TAbs  (s : {bind type in term})
| TApp  (s : term) (A : type).

(** **** Substitution Lemmas *)

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.

Instance SubstLemmas_type : SubstLemmas type. derive. Qed.

Instance HSubst_term : HSubst type term. derive. Defined.

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.

Instance HSubstLemmas_term : HSubstLemmas type term. derive. Qed.
Instance SubstHSubstComp_type_term : SubstHSubstComp type term. derive. Qed.

Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

(** **** One-Step Reduction *)

Inductive step : term -> term -> Prop :=
| step_beta (A : type) (s t : term) :
    step (App (Abs A s) t) s.[t/]
| step_inst (A : type) (s : term) :
    step (TApp (TAbs s) A) s.|[A/]
| step_appL s1 s2 t :
    step s1 s2 -> step (App s1 t) (App s2 t)
| step_appR s t1 t2 :
    step t1 t2 -> step (App s t1) (App s t2)
| step_abs A s1 s2 :
    step s1 s2 -> step (Abs A s1) (Abs A s2)
| step_tapp A s1 s2 :
    step s1 s2 -> step (TApp s1 A) (TApp s2 A)
| step_tabs s1 s2 :
    step s1 s2 -> step (TAbs s1) (TAbs s2).

Lemma step_ebeta A s t u : u = s.[t/] -> step (App (Abs A s) t) u.
Proof. move->. exact: step_beta. Qed.

Lemma step_einst A s t : t = s.|[A/] -> step (TApp (TAbs s) A) t.
Proof. move->. exact: step_inst. Qed.

Lemma step_substf theta sigma s t :
  step s t -> step s.|[theta].[sigma] t.|[theta].[sigma].
Proof.
  move=> st. elim: st sigma theta => {s t}; asimpl; eauto using step.
  - move=> A s t sigma theta. apply: step_ebeta. by autosubst.
  - move=> A s sigma theta. apply: step_einst. by autosubst.
Qed.

Lemma step_subst sigma s t : step s t -> step s.[sigma] t.[sigma].
Proof. move=> h. apply (step_substf ids sigma) in h. by asimpl in h. Qed.

Lemma step_hsubst theta s t : step s t -> step s.|[theta] t.|[theta].
Proof. move=> h. apply (step_substf theta ids) in h. by asimpl in h. Qed.

(** **** Many-Step Reduction *)

Inductive red (s : term) : term -> Prop :=
| redR : red s s
| redS t u : red s t -> step t u -> red s u.
Hint Resolve redR.

Lemma red_trans y x z : red x y -> red y z -> red x z.
Proof. move=> A. elim=> //={z} y' z _. exact: redS. Qed.

Lemma red_hom h :
  (forall x y, step x y -> step (h x) (h y)) ->
  (forall x y, red x y -> red (h x) (h y)).
Proof.
  move=> A x y. elim=> [|y' z _ B /A]; eauto using red.
Qed.

Definition sred sigma tau :=
  forall x : var, red (sigma x) (tau x).

Lemma red_app s1 s2 t1 t2 :
  red s1 s2 -> red t1 t2 -> red (App s1 t1) (App s2 t2).
Proof.
  move=> A B. apply: (@red_trans (App s2 t1)).
  - apply: (@red_hom (App^~ t1)) A => x y. exact: step_appL.
  - apply: red_hom B => x y. exact: step_appR.
Qed.

Lemma red_abs A s1 s2 : red s1 s2 -> red (Abs A s1) (Abs A s2).
Proof. apply: red_hom => x y. exact: step_abs. Qed.

Lemma red_tapp A s1 s2 : red s1 s2 -> red (TApp s1 A) (TApp s2 A).
Proof. apply: (@red_hom (TApp^~A)) => x y. exact: step_tapp. Qed.

Lemma red_tabs s1 s2 : red s1 s2 -> red (TAbs s1) (TAbs s2).
Proof. apply: red_hom => x y. exact: step_tabs. Qed.

Lemma red_subst sigma s t : red s t -> red s.[sigma] t.[sigma].
Proof. apply: red_hom => x y. exact: step_subst. Qed.

Lemma red_hsubst theta s t : red s t -> red s.|[theta] t.|[theta].
Proof. apply: red_hom => x y. exact: step_hsubst. Qed.

Lemma sred_up sigma tau : sred sigma tau -> sred (up sigma) (up tau).
Proof. move=> A [|n] //=. asimpl. apply/red_subst/A. Qed.

Lemma sred_hup sigma tau theta :
  sred sigma tau -> sred (sigma >>| theta) (tau >>| theta).
Proof. move=> A n /=. apply/red_hsubst/A. Qed.

Hint Resolve red_app red_abs red_tapp red_tabs sred_up sred_hup : red_congr.

Lemma red_compat sigma tau s :
  sred sigma tau -> red s.[sigma] s.[tau].
Proof.
  elim: s sigma tau; intros; asimpl; eauto with red_congr.
Qed.

Lemma red_beta s t1 t2 : step t1 t2 -> red s.[t1/] s.[t2/].
Proof. move=> h. apply: red_compat => -[]; eauto using red. Qed.

(** **** Syntactic typing *)

Definition ctx := seq type.
Local Notation "Gamma `_ i" := (nth (ids 0) Gamma i).
Definition raise (Gamma : ctx) := [seq A.[ren (+1)] | A <- Gamma].

Inductive has_type (Gamma : ctx) : term -> type -> Prop :=
| ty_var (x : var) :
    x < size Gamma -> has_type Gamma (TeVar x) Gamma`_x
| ty_abs (A B : type) (s : term) :
    has_type (A :: Gamma) s B ->
    has_type Gamma (Abs A s) (Arr A B)
| ty_app (A B : type) (s t : term) :
    has_type Gamma s (Arr A B) ->
    has_type Gamma t A ->
    has_type Gamma (App s t) B
| ty_tabs (A : type) (s : term) :
    has_type (raise Gamma) s A ->
    has_type Gamma (TAbs s) (All A)
| ty_tapp (A B : type) (s : term) :
    has_type Gamma s (All A) ->
    has_type Gamma (TApp s B) A.[B/].

(* Strong Normalization *)

Inductive sn x : Prop :=
| SNI : (forall y, step x y -> sn y) -> sn x.

Lemma sn_preimage h x :
  (forall x y, step x y -> step (h x) (h y)) -> sn (h x) -> sn x.
Proof.
  move eqn:(h x) => v A B. elim: B h x A eqn => {v} v _ ih h x A eqn.
  apply: SNI => y /A. rewrite eqn => /ih; eauto.
Qed.

Lemma sn_closed t s : sn (App s t) -> sn s.
Proof. apply: (sn_preimage (h := App^~t)) => x y. exact: step_appL. Qed.

Lemma sn_tclosed A s : sn (TApp s A) -> sn s.
Proof. apply: (sn_preimage (h := TApp^~A)) => x y. exact: step_tapp. Qed.

Lemma sn_preservation s t : sn s -> step s t -> sn t.
Proof. by move=> [f] /f. Qed.

Lemma sn_subst sigma s : sn s.[sigma] -> sn s.
Proof. apply: sn_preimage => x y. exact: step_subst. Qed.

Lemma sn_hsubst theta s : sn s.|[theta] -> sn s.
Proof. apply: sn_preimage => x y. exact: step_hsubst. Qed.

(* The Reducibility Candidates/Logical Predicate*)

Definition cand := term -> Prop.

Definition neutral (s : term) : bool :=
  match s with
    | Abs _ _ | TAbs _ => false
    | _ => true
  end.

Record reducible (P : cand) : Prop := {
  p_sn : forall s, P s -> sn s;
  p_cl : forall s t, P s -> step s t -> P t;
  p_nc : forall s, neutral s -> (forall t, step s t -> P t) -> P s
}.

Fixpoint L (T : type) (rho : nat -> cand) : cand :=
  match T with
    | TyVar x => rho x
    | Arr A B => fun s => forall t, L A rho t -> L B rho (App s t)
    | All A => fun s => forall P B, reducible P -> L A (P .: rho) (TApp s B)
  end.

Definition EL E (rho : nat -> cand) (sigma : var -> term) : Prop :=
  forall x, x < size E -> L E`_x rho (sigma x).

Definition admissible (rho : nat -> cand) :=
  forall x, reducible (rho x).

(* Facts about reducible sets. *)

Lemma reducible_sn : reducible sn.
Proof. constructor; eauto using sn. by move=> s t [f] /f. Qed.
Hint Resolve reducible_sn.

Lemma reducible_var P x : reducible P -> P (TeVar x).
Proof. move/p_nc. apply=> // t st. inv st. Qed.

Lemma ad_cons P rho :
  reducible P -> admissible rho -> admissible (P .: rho).
Proof. by move=> H1 H2 [|i] //=. Qed.

Lemma L_reducible T rho :
  admissible rho -> reducible (L T rho).
Proof with eauto using step.
  elim: T rho => /=[i|A ih1 B ih2|A ih] rho safe...
  - constructor.
    + move=> s h. apply: (@sn_closed (TeVar 0)). apply: (p_sn (P := L B rho))...
      apply/h/reducible_var...
    + move=> s t h st u la. apply: (p_cl _ (s := App s u))...
    + move=> s ns h t la. have snt := p_sn (ih1 _ safe) la.
      elim: snt la => {t} t _ ih3 la. apply: p_nc... move=> v st. inv st=> //...
      apply: ih3 => //. exact: (p_cl (ih1 _ safe)) la _.
  - constructor.
    + move=> s /(_ sn (TyVar 0) reducible_sn)/p_sn/sn_tclosed; apply.
      by apply/ih/ad_cons...
    + move=> s t h st P B rep. apply: p_cl (step_tapp B st)...
      by apply/ih/ad_cons.
    + move=> s ns h P B rep. apply ih... exact: ad_cons.
      move=> t st. inv st => //...
Qed.

Corollary L_sn A rho s : admissible rho -> L A rho s -> sn s.
Proof. move=> /L_reducible/p_sn. apply. Qed.

Corollary L_cl T rho s t : admissible rho -> L T rho s -> step s t -> L T rho t.
Proof. move=> /L_reducible/p_cl. apply. Qed.

Corollary L_nc T rho s :
  admissible rho -> neutral s -> (forall t, step s t -> L T rho t) -> L T rho s.
Proof. move=> /L_reducible/p_nc. apply. Qed.

Corollary L_var T rho x : admissible rho -> L T rho (TeVar x).
Proof. move=> /L_nc. apply=> // t st. inv st. Qed.

Corollary L_cl_star T rho s t :
  admissible rho -> L T rho s -> red s t -> L T rho t.
Proof. move=> /L_cl cl H st. elim: st H; eauto. Qed.

(* Closure under beta expansion. *)

Lemma beta_expansion A B rho s t :
  admissible rho -> sn t -> L A rho s.[t/] ->
  L A rho (App (Abs B s) t).
Proof with eauto.
  move=> ad snt h. have sns := sn_subst (L_sn ad h).
  elim: sns t snt h => {s} s sns ih1 t. elim=> {t} t snt ih2 h.
  apply: L_nc => // u st. inv st => //.
  - inv H2. apply: ih1 => //. apply: L_cl ad h _. exact: step_subst.
  - apply: ih2 => //. apply: L_cl_star ad h _. exact: red_beta.
Qed.

Lemma inst_expansion A B rho s :
  admissible rho -> L A rho s.|[B/] -> L A rho (TApp (TAbs s) B).
Proof.
  move=> ad h. have sns := sn_hsubst (L_sn ad h). elim: sns h.
  move=> {s} s _ ih h. apply: L_nc => // t st. inv st => //.
  inv H2 => //. apply: ih => //. apply: L_cl ad h _. exact: step_hsubst.
Qed.

(* The type substitution lemma. *)

Lemma extend_ext (rho tau : nat -> cand) :
  (forall i s, rho i s <-> tau i s) ->
  (forall P i s, (P .: rho) i s <-> (P .: tau) i s).
Proof. by move=>h P[]/=. Qed.

Lemma L_ext T rho tau :
  (forall i s, rho i s <-> tau i s) -> (forall s, L T rho s <-> L T tau s).
Proof.
  elim: T rho tau => //=[T1 IH1 T2 IH2|T IH] rho tau E s.
  - split=> H1 t H2.
    + rewrite -(IH2 _ _ E). apply: H1. by rewrite (IH1 _ _ E).
    + rewrite (IH2 _ _ E). apply: H1. by rewrite -(IH1 _ _ E).
  - move: E => /extend_ext E. split=> H P B /H.
    + move=> /(_ B). by rewrite (IH _ _ (E P)).
    + move=> /(_ B). by rewrite -(IH _ _ (E P)).
Qed.

Lemma L_ren A rho xi s :
  L A.[ren xi] rho s <-> L A (xi >>> rho) s.
Proof with intuition.
  elim: A rho xi s => [x|A ih1 B ih2|A ih] rho xi s; asimpl => //.
  - split=> h1 t h2. rewrite -ih2. apply: h1. by rewrite ih1.
    rewrite ih2. apply: h1. by rewrite -ih1.
  - split=> h P B r. move: (h _ B r). rewrite ih. apply L_ext. by case.
    rewrite ih. asimpl. exact: h.
Qed.

Lemma L_weaken A P rho s : L A.[ren (+1)] (P .: rho) s <-> L A rho s.
Proof. exact: L_ren. Qed.

Lemma L_subst A rho sigma s :
  L A.[sigma] rho s <-> L A (fun i => L (sigma i) rho) s.
Proof.
  elim: A rho sigma s => [x|A ih1 B ih2|A ih] rho sigma s; asimpl=>//.
  - split=> h1 t h2. rewrite -ih2. apply: h1. by rewrite ih1.
    rewrite ih2. apply h1. by rewrite -ih1.
  - split=> h P B /(h _ B); rewrite ih; apply L_ext => -[|x] //= t; asimpl;
    by rewrite L_weaken.
Qed.

(* The fundamental theorem. *)

Theorem soundness Gamma s A :
  has_type Gamma s A -> forall rho theta sigma,
    admissible rho -> EL Gamma rho sigma -> L A rho s.|[theta].[sigma].
Proof with eauto using L_sn, ad_cons.
  elim=> {Gamma s A} [|Gamma A B s _ ih||Gamma A s _ ih|Gamma A B s _ /=ih]
    rho theta sigma ad el; asimpl...
  - move=> t h. apply: beta_expansion... asimpl. apply: ih... by case.
  - move=> P B h. apply: inst_expansion... asimpl. apply: ih... move=> x.
    rewrite size_map => lt. rewrite (nth_map (ids 0)) // L_weaken...
  - rewrite L_subst. specialize (ih _ theta sigma ad el (L B rho) B.[theta]).
    have/ih: reducible (L B rho). exact: L_reducible. apply L_ext. by case.
Qed.

Lemma rho_id : admissible (fun _ => sn).
Proof. move=> x /=. exact: reducible_sn. Qed.

Corollary type_L E s T rho : has_type E s T -> admissible rho -> L T rho s.
Proof.
  move=> ty ad. move: (@soundness E s T ty rho) => h.
  specialize (h ids ids ad). asimpl in h. apply: h => x B. exact: L_var.
Qed.

Corollary strong_normalization E s T : has_type E s T -> sn s.
Proof. move=>/type_L/(_ rho_id)/L_sn. apply. exact: rho_id. Qed.
