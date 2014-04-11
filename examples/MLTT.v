(** * Martin-Löf Type Theory 

  We will prove confluence and type preservation.
*)


Require Import Autosubst MMap Size Lib Decidable Contexts.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** **** The (Curry style) calculus of constructions with a hierarchy of predicative universes. *)

Inductive term : Type :=
| TVar (x : var)
| Sort (n : nat)
| App  (s t : term)
| Lam  (s : {bind term})
| Prod (s : term) (t : {bind term}).

Instance VarConstr_term : VarConstr term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

(** **** One-Step Reduction *)

Inductive step : term -> term -> Prop :=
| step_beta s t u :
    u = s.[t .: Var] -> step (App (Lam s) t) u
| step_appL s1 s2 t :
    step s1 s2 -> step (App s1 t) (App s2 t)
| step_appR s t1 t2 :
    step t1 t2 -> step (App s t1) (App s t2)
| step_lam s1 s2 :
    step s1 s2 -> step (Lam s1) (Lam s2)
| step_prodL A1 A2 B :
    step A1 A2 -> step (Prod A1 B) (Prod A2 B)
| step_prodR A B1 B2 :
    step B1 B2 -> step (Prod A B1) (Prod A B2).

Notation red := (star step).
Notation "s === t" := (conv step s t) (at level 50).

Definition sred sigma tau :=
  forall x : var, red (sigma x) (tau x).

Lemma step_subst sigma s t : step s t -> step s.[sigma] t.[sigma].
Proof.
  move=> st. elim: st sigma => /={s t}; eauto using step.
  move=> s t u -> sigma; apply: step_beta; by autosubst.
Qed.

(** **** Many-Step Reduction *)

Lemma red_app s1 s2 t1 t2 :
  red s1 s2 -> red t1 t2 -> red (App s1 t1) (App s2 t2).
Proof.
  move=> A B. apply: (star_trans (App s2 t1)).
  - apply: (star_hom (App^~ t1)) A => x y. exact: step_appL.
  - apply: star_hom B => x y. exact: step_appR.
Qed.

Lemma red_lam s1 s2 :
  red s1 s2 -> red (Lam s1) (Lam s2).
Proof.
  apply: star_hom => x y. exact: step_lam.
Qed.

Lemma red_prod s1 s2 t1 t2 :
  red s1 s2 -> red t1 t2 -> red (Prod s1 t1) (Prod s2 t2).
Proof.
  move=> A B. apply: (star_trans (Prod s2 t1)).
  - apply: (star_hom (Prod^~ t1)) A => x y. exact: step_prodL.
  - apply: star_hom B => x y. exact: step_prodR.
Qed.

Lemma red_subst sigma s t :
  red s t -> red s.[sigma] t.[sigma].
Proof.
  apply: star_hom. exact: step_subst.
Qed.

Lemma sred_up sigma tau :
  sred sigma tau -> sred (up sigma) (up tau).
Proof.
  move=> A [|n] //=. apply: red_subst. exact: A.
Qed.

Hint Resolve red_app red_lam red_prod sred_up : red_congr.

Lemma red_compat sigma tau s :
  sred sigma tau -> red s.[sigma] s.[tau].
Proof.
  elim: s sigma tau => *; autosubst; eauto with red_congr.
Qed.

(** **** Conversion *)

Definition sconv (sigma tau : var -> term) :=
  forall x, sigma x === tau x.

Lemma conv_app s1 s2 t1 t2 :
  s1 === s2 -> t1 === t2 -> App s1 t1 === App s2 t2.
Proof.
  move=> A B. apply: (conv_trans (App s2 t1)).
  - apply: (conv_hom (App^~ t1)) A => x y. exact: step_appL.
  - apply: conv_hom B => x y. exact: step_appR.
Qed.

Lemma conv_lam s1 s2 :
  s1 === s2 -> Lam s1 === Lam s2.
Proof.
  apply: conv_hom => x y. exact: step_lam.
Qed.

Lemma conv_prod s1 s2 t1 t2 :
  s1 === s2 -> t1 === t2 -> Prod s1 t1 === Prod s2 t2.
Proof.
  move=> A B. apply: (conv_trans (Prod s2 t1)).
  - apply: (conv_hom (Prod^~ t1)) A => x y. exact: step_prodL.
  - apply: conv_hom B => x y. exact: step_prodR.
Qed.

Lemma conv_subst sigma s t :
  s === t -> s.[sigma] === t.[sigma].
Proof.
  apply: conv_hom. exact: step_subst.
Qed.

Lemma sconv_up sigma tau :
  sconv sigma tau -> sconv (up sigma) (up tau).
Proof.
  move=> A [|x] //=. exact: conv_subst.
Qed.

Lemma conv_compat sigma tau s :
  sconv sigma tau -> s.[sigma] === s.[tau].
Proof.
  elim: s sigma tau => *; autosubst; eauto using
    conv_app, conv_lam, conv_prod, sconv_up.
Qed.

Lemma conv_beta s t1 t2 :
  t1 === t2 -> s.[t1.:Var] === s.[t2.:Var].
Proof.
  move=> c. by apply: conv_compat => -[].
Qed.

(** **** Church-Rosser theorem *)

Inductive pstep : term -> term -> Prop :=
| pstep_beta s1 s2 t1 t2 u :
    u = s2.[t2 .: Var] ->
    pstep s1 s2 -> pstep t1 t2 -> pstep (App (Lam s1) t1) u
| pstep_var x : pstep (Var x) (Var x)
| pstep_sort n : pstep (Sort n) (Sort n)
| pstep_app s1 s2 t1 t2 :
    pstep s1 s2 -> pstep t1 t2 -> pstep (App s1 t1) (App s2 t2)
| pstep_lam s1 s2 :
    pstep s1 s2 -> pstep (Lam s1) (Lam s2)
| pstep_prod s1 s2 t1 t2 :
    pstep s1 s2 -> pstep t1 t2 -> pstep (Prod s1 t1) (Prod s2 t2).

Definition psstep (sigma tau : var -> term) :=
  forall x, pstep (sigma x) (tau x).

Fixpoint rho (s : term) : term :=
  match s with
    | App (Lam s) t => (rho s).[rho t .: Var]
    | App s t => App (rho s) (rho t)
    | Lam s => Lam (rho s)
    | Prod A B => Prod (rho A) (rho B)
    | x => x
  end.

Lemma pstep_refl s : pstep s s.
Proof. elim: s; eauto using pstep. Qed.
Hint Resolve pstep_refl.

Lemma step_pstep s t : step s t -> pstep s t.
Proof. elim; eauto using pstep. Qed.

Lemma pstep_red s t : pstep s t -> red s t.
Proof.
  elim=> {s t} //=; eauto with red_congr.
  move=> s1 s2 t1 t2 u -> {u} _ A _ B. eapply starES. by econstructor.
  apply: (star_trans (s2.[t1.:Var])). exact: red_subst.
  by apply: red_compat => -[|].
Qed.

Lemma pstep_subst sigma s t :
  pstep s t -> pstep s.[sigma] t.[sigma].
Proof.
  move=> A. elim: A sigma => /=; eauto using pstep.
  move=> s1 s2 t1 t2 u -> _ A _ B sigma. eapply pstep_beta; eauto. by autosubst.
Qed.

Lemma psstep_up sigma tau :
  psstep sigma tau -> psstep (up sigma) (up tau).
Proof.
  move=> A [|n] //=. apply: pstep_subst. exact: A.
Qed.

Lemma pstep_compat sigma tau s t :
  psstep sigma tau -> pstep s t -> pstep s.[sigma] t.[tau].
Proof with eauto using pstep, psstep_up.
  move=> A B. elim: B sigma tau A; autosubst...
  move=> s1 s2 t1 t2 u -> _ A _ B sigma tau C.
  apply: (@pstep_beta _ (s2.[up tau]) _ (t2.[tau])); autosubst...
Qed.

Lemma pstep_compat_beta s1 s2 t1 t2 :
  pstep s1 s2 -> pstep t1 t2 -> pstep s1.[t1.:Var] s2.[t2.:Var].
Proof.
  move=> A B. by apply: pstep_compat A => -[|].
Qed.

Lemma rho_triangle : triangle pstep rho.
Proof with eauto using pstep.
  move=> s t. elim=> {s t} //=...
  - move=> s1 s2 t1 t2 u -> {u} _ A _ B. exact: pstep_compat_beta.
  - move=> s1 s2 t1 t2 A ih1 _ ih2. case: s1 A ih1 => //=...
    move=> s A ih1. inv A. inv ih1...
Qed.

Theorem church_rosser :
  CR step.
Proof.
  apply: (cr_method (e2 := pstep) (rho := rho)).
    exact: step_pstep. exact: pstep_red. exact: rho_triangle.
Qed.
Hint Resolve church_rosser.

(** **** Reduction behaviour *)

Lemma normal_step_sort n : normal step (Sort n).
Proof. move=> [s st]. inv st. Qed.
Hint Resolve normal_step_sort.

CoInductive RedProdSpec A1 B1 : term -> Prop :=
| RedProdSpecI A2 B2 : red A1 A2 -> red B1 B2 -> RedProdSpec A1 B1 (Prod A2 B2).

Lemma red_prod_inv A1 B1 C :
  red (Prod A1 B1) C -> RedProdSpec A1 B1 C.
Proof.
  elim=> {C} [|C D _ [A2 B2]].
  - by constructor.
  - move=> ra12 rb12 st. inv st; constructor; eauto using star.
Qed.

Lemma inj_sort n m : conv step (Sort n) (Sort m) -> n = m.
Proof.
  move=> A. suff: (Sort n = Sort m) => [[//]|].
  eapply cr_conv_normal => //; done.
Qed.

Lemma inj_prod A1 A2 B1 B2 :
  conv step (Prod A1 B1) (Prod A2 B2) -> conv step A1 A2 /\ conv step B1 B2.
Proof.
  move=>/church_rosser[z /red_prod_inv s1 /red_prod_inv s2].
  inv s1; inv s2; split; eauto using join_conv.
Qed.

Lemma conv_prod_sort A B n :
  ~conv step (Prod A B) (Sort n).
Proof.
  move=> h. apply cr_star_normal in h => //. apply red_prod_inv in h. inv h.
Qed.

(** **** Typing *)

Inductive sub : term -> term -> Prop :=
| sub_sort n m : n <= m -> sub (Sort n) (Sort m)
| sub_prod A B1 B2 : sub B1 B2 -> sub (Prod A B1) (Prod A B2).

Fixpoint get (Gamma : list term) (n : var) {struct n}: term :=
  match Gamma, n with
    | [::], _ => Var 0
    | A :: _, 0 => A.[ren (+1)]
    | _ :: Gamma, n.+1 => (get Gamma n).[ren (+1)]
  end.
Arguments get Gamma n.


Notation "Gamma `_ i" := (get Gamma i).
Infix "<:" := sub (at level 50, no associativity).

Inductive ty : list term -> term -> term -> Prop :=
| ty_var Gamma x :
    ok Gamma -> x < size Gamma -> ty Gamma (TVar x) Gamma`_x
| ty_sort Gamma n  :
    ok Gamma -> ty Gamma (Sort n) (Sort n.+1)
| ty_app Gamma A B s t u :
    u = B.[t.:Var] ->
    ty Gamma s (Prod A B) ->
    ty Gamma t A ->
    ty Gamma (App s t) u
| ty_lam' Gamma A B s n :
    ty Gamma A (Sort n) ->
    ty (A::Gamma) s B ->
    ty Gamma (Lam s) (Prod A B)
| ty_prod Gamma A B n :
    ty Gamma A (Sort n) ->
    ty (A :: Gamma) B (Sort n) ->
    ty Gamma (Prod A B) (Sort n)
| ty_conv Gamma s A B n :
    ty Gamma s A -> A === B -> ty Gamma B (Sort n) -> ty Gamma s B
| ty_sub Gamma s A B :
    ty Gamma s A -> A <: B -> ty Gamma s B
with ok : list term -> Prop :=
| ok_nil : ok [::]
| ok_cons Gamma A n : ok Gamma -> ty Gamma A (Sort n) -> ok (A :: Gamma).

Lemma sub_subst sigma A B :
  A <: B -> A.[sigma] <: B.[sigma].
Proof.
  move=> s. elim: s sigma; eauto using sub.
Qed.

Notation "[ Gamma |- ]" := (ok Gamma).
Notation "[ Gamma |- s :- A ]" := (ty Gamma s A).

Lemma ty_ok Gamma (s : term) A : [Gamma |- s :- A] -> [Gamma |-].
Proof. by elim. Qed.

Lemma ty_lam Gamma A B s :
  [ A :: Gamma |- s :- B ] -> [ Gamma |- Lam s :- Prod A B ].
Proof.
  move=> tp. move: (tp) => /ty_ok okg. inv okg. eauto using ty.
Qed.

Lemma ty_renaming xi Gamma Delta s A :
  [ Gamma |- s :- A ] ->
  [ Delta |- ] ->
  (forall x, x < size Gamma -> xi x < size Delta) ->
  (forall x, x < size Gamma -> (Gamma`_x).[ren xi] = Delta`_(xi x)) ->
  [ Delta |- s.[ren xi] :- A.[ren xi] ].
Proof.
  move=> tp. elim: tp xi Delta => {Gamma s A} /=
    [Gamma x _ si|Gamma n _|Gamma A B s t u->{u} _ ih1 _ ih2|
     Gamma A B s n _ ih1 _ ih2|Gamma A B n _ ih1 _ ih2|
     Gamma A B s n _ ih1 conv _ ih2|Gamma A B s _ ih sub] xi Delta wf subctx eqn; autosubst.
  - rewrite eqn //. apply: ty_var => //. exact: subctx.
  - exact: ty_sort wf.
  - apply: (@ty_app _ A.[ren xi] B.[up (ren xi)]). by autosubst.
      exact: ih1. exact: ih2.
  - assert (ty : [Delta |- A.[ren xi] :- Sort n]). by eapply ih1.
    apply: ty_lam. apply ih2.
    + exact: ok_cons ty.
    + by move=> [|x] //=/subctx.
    + move=> [_|x] //=. by autosubst. move=> /eqn <-. by autosubst.
  - assert (ty : [Delta |- A.[ren xi] :- Sort n]). exact: ih1.
    apply: ty_prod => //. apply: ih2.
    + exact: ok_cons ty.
    + by move=> [|x] //=/subctx.
    + move=> [_|x]/=. by autosubst. move=> /eqn <-. by autosubst.
  - eapply ty_conv. by eapply ih1. exact: conv_subst. by eapply ih2.
  - eapply ty_sub. by eapply ih. exact: sub_subst.
Qed.

Lemma weakening Gamma s A B n :
  [ Gamma |- s :- A ] -> [ Gamma |- B :- Sort n ] ->
  [ B :: Gamma |- s.[ren (+1)] :- A.[ren (+1)] ].
Proof.
  move=> ty1 ty2. apply: (ty_renaming ty1) => //.
  apply: ok_cons (ty2). exact: ty_ok ty2.
Qed.

Lemma weakenings Gamma s s' A A' B n :
  s' = s.[ren (+1)] -> A' = A.[ren (+1)] ->
  ty Gamma B (Sort n) -> ty Gamma s A -> ty (B :: Gamma) s' A'.
Proof.
  move=> e1 e2 okd tp. subst. exact: weakening tp okd.
Qed.

Lemma context_ok Gamma x :
  [ Gamma |- ] -> x < size Gamma -> exists n, [ Gamma |- Gamma`_x :- Sort n ].
Proof.
  move=> okg. elim: okg x => //={Gamma} Gamma A n _ ih h [_|x /ih[m {ih} ih]].
  - exists n => /=. exact: weakening h (h).
  - exists m => /=. exact: weakening ih h.
Qed.

Lemma ty_subst sigma Gamma Delta s A :
  [ Gamma |- s :- A ] ->
  [ Delta |- ] ->
  (forall x, x < size Gamma -> [ Delta |- sigma x :- (Gamma`_x).[sigma] ]) ->
  [ Delta |- s.[sigma] :- A.[sigma] ].
Proof.
  move=> tp. elim: tp sigma Delta => {Gamma s A} /=
    [Gamma x _ si|Gamma n _|Gamma A B s t u->{u} _ ih1 _ ih2|
     Gamma A B s n _ ih1 _ ih2|Gamma A B n _ ih1 _ ih2|
     Gamma A B s n _ ih1 conv _ ih2|Gamma A B s _ ih sub] sigma Delta wf cty; autosubst in *.
  - exact: cty.
  - exact: ty_sort.
  - apply: (@ty_app _ A.[sigma] B.[up sigma]). by autosubst.
      exact: ih1. exact: ih2.
  - apply: ty_lam. apply: ih2. apply: ok_cons => //. by eapply ih1.
    move=> [_|x /=/cty] //=. autosubst. rewrite -subst_comp. apply: ty_var => //.
    apply: ok_cons => //. by eapply ih1. eapply weakenings; autosubst=> //.
    by eapply ih1.
  - apply: ty_prod. exact: ih1. apply ih2. apply: ok_cons => //. by eapply ih1.
    move=> [_|x /=/cty] /=. autosubst. rewrite -subst_comp. apply: ty_var => //.
    apply: ok_cons => //. by eapply ih1. eapply weakenings; autosubst=> //. by eapply ih1.
  - eapply ty_conv. by eapply ih1. exact: conv_subst. by eapply ih2.
  - eapply ty_sub. by eapply ih. exact: sub_subst.
Qed.

Lemma ty_subst1 Gamma s t A B s' B' :
  s' = s.[t.:Var] -> B' = B.[t.:Var] ->
  [ A :: Gamma |- s :- B ] -> [ Gamma |- t :- A ] ->
  [ Gamma |- s' :- B' ].
Proof.
  move=> e1 e2 ty1 ty2. subst. apply: (ty_subst ty1).
  - exact: ty_ok ty2.
  - move=> [_|x le]; autosubst => //. apply: ty_var => //. exact: ty_ok ty2.
Qed.

Lemma ty_ctx_conv Gamma s A B C n :
  [ A :: Gamma |- s :- C ] -> B === A -> [ Gamma |- B :- Sort n ] ->
  [ B :: Gamma |- s :- C ].
Proof.
  move=> tp1 con tp2.
  have[m tp3]: exists m, [ Gamma |- A :- Sort m ].
    move: tp1 => /ty_ok ok1. inv ok1; by eauto.
  have okgb: [ B :: Gamma |- ].
    apply: ok_cons (tp2). exact: ty_ok tp2.
  rewrite -[s]subst_id -[C]subst_id. apply: (ty_subst tp1) => // -[_|x dom] //=; autosubst.
  - eapply (ty_conv (n := m)). by eapply ty_var. exact: conv_subst. exact: weakening tp3 tp2.
  - exact: ty_var.
Qed.

Lemma ty_prod_inv' Gamma A B m n s t :
  ty Gamma s t -> s = (Prod A B) -> conv step t (Sort m) -> m <= n ->
    ty Gamma A (Sort n) /\ ty (A :: Gamma) B (Sort n).
Proof.
  move=> tp. elim: tp A B n m => // {Gamma s t}.
  - move=> Gamma A B n tp1 _ tp2 _ A' B' m n' [<-<-] /inj_sort <- le_n_m.
    split. apply: ty_sub tp1 _. exact: sub_sort. apply: ty_sub tp2 _.
    exact: sub_sort.
  - move=> Gamma s A B n _ ih con _ _ A' B' n' m e1 e2 le_m_n'.
    apply: ih e1 _ le_m_n'. exact: conv_trans con _.
  - move=> Gamma s A B _ ih sb A' B' n m e1 e2 le_m_n. inv sb.
    + move: e2 => /inj_sort e2. subst. eapply ih. reflexivity.
      econstructor. exact: leq_trans _ le_m_n.
    + exfalso. exact: conv_prod_sort e2.
Qed.

Lemma ty_prod_inv Gamma A B n :
  ty Gamma (Prod A B) (Sort n) ->
    ty Gamma A (Sort n) /\ ty (A :: Gamma) B (Sort n).
Proof.
  move=> h. exact: ty_prod_inv' h _ _ _.
Qed.

Lemma ty_sort_inv' Gamma n A :
  ty Gamma (Sort n) A -> exists2 m, n < m & conv step (Sort m) A.
Proof.
  move e:(Sort n) => s tp. elim: tp n e => // {Gamma s A}.
  - move=> Gamma n okg m [->]. by exists n.+1.
  - move=> Gamma s A B n _ ih con _ _ m e. case: (ih _ e) => k h1 h2.
    exists k => //. exact: conv_trans con.
  - move=> Gamma s A B _ ih sb n e. case: (ih _ e) => k h1 h2. inv sb.
    + move: h2 => /inj_sort h2. subst. exists m => //. exact: leq_trans h1 _.
    + exfalso. exact: conv_prod_sort (conv_sym h2).
Qed.

Lemma ty_sort_inv Gamma n m :
  ty Gamma (Sort n) (Sort m) -> n < m.
Proof.
  by move=> /ty_sort_inv'[k h1 /inj_sort<-].
Qed.

Lemma ty_prod_maxn Gamma A B n m :
  [ Gamma |- A :- Sort n ] -> [ A :: Gamma |- B :- Sort m ] ->
  [ Gamma |- Prod A B :- Sort (maxn n m) ].
Proof.
  move=> ty1 ty2. apply: ty_prod.
  - apply: (ty_sub ty1). apply: sub_sort. exact: leq_maxl.
  - apply: (ty_sub ty2). apply: sub_sort. exact: leq_maxr.
Qed.

Lemma sub_preservation Gamma A B n :
  A <: B -> [ Gamma |- A :- Sort n ] -> exists m, [ Gamma |- B :- Sort m ].
Proof.
  move=> s. elim: s Gamma n => {A B} [_ m _ Gamma _ /ty_ok ok|
    A B1 B2 _ ih Gamma n /ty_prod_inv[tp1 /ih [m tp2]]].
  - exists m.+1. exact: ty_sort.
  - exists (maxn n m). apply: ty_prod_maxn tp1 tp2.
Qed.

Lemma propagation Gamma s A :
  ty Gamma s A -> exists n, ty Gamma A (Sort n).
Proof.
  elim=> {Gamma s A} /=
    [Gamma x|Gamma n ok|Gamma A B s t u->{u} _ [n /ty_prod_inv[_ ih]] h _|
     Gamma A B s n tp _ _ [m ih]|Gamma A B n _ ih1 _ ih2|
     Gamma A B s n _ _ _ h _|Gamma A B s _ [n ih] sub] //=.
  - by move=> /context_ok h /h.
  - exists n.+2. exact: ty_sort.
  - exists n. exact: ty_subst1 ih h.
  - exists (maxn n m). exact: ty_prod_maxn tp ih.
  - by exists n.
  - exact: sub_preservation sub ih.
Qed.

Lemma ty_lam_inv' Gamma s A B C :
  [ Gamma |- Lam s :- C ] -> Prod A B === C ->
    forall n1 n2, [ Gamma |- A :- Sort n1 ] -> [ A :: Gamma |- B :- Sort n2 ] ->
      [ A :: Gamma |- s :- B ].
Proof.
  move e:(Lam s) => t tp. elim: tp A B s e => // {Gamma t C}.
  - move=> Gamma A B s n _ _ tp _ A' B' t [->] {t} /inj_prod[con1 con2].
    move=> n1 n2 tp1 tp2. apply: ty_conv (conv_sym con2) tp2.
    exact: ty_ctx_conv con1 tp1.
  - move=> Gamma s A B n _ ih con1 _ _ A' B' t e con2 n1 n2 tp1 tp2.
    eapply ih => //. apply: conv_trans con2 _. exact: conv_sym.
    eassumption. eassumption.
  - move=> Gamma s A B i ih sb A' B' t e con n1 n2 tp1 tp2. destruct sb.
    + exfalso. eapply conv_prod_sort; eauto.
    + move: con => /inj_prod[con1 con2].
      have[n3 tp3]: exists n3, ty (A' :: Gamma) B1 (Sort n3).
        move: (propagation i) => [n /ty_prod_inv[_ tp3]]. exists n.
        exact: ty_ctx_conv tp3 con1 tp1.
      move: (tp2). eapply ty_conv. Focus 2. apply conv_sym. eassumption.
      apply: ty_sub (sb). apply: ih tp1 _; eauto.
      exact: conv_prod.
Qed.

Lemma ty_lam_inv Gamma s A B :
  [ Gamma |- Lam s :- Prod A B ] -> [ A :: Gamma |- s :- B ].
Proof.
  move=> tp. move: (propagation tp) => [n] /ty_prod_inv[tp1 tp2].
  exact: ty_lam_inv' tp _ _ _ tp1 tp2.
Qed.

Lemma subject_reduction Gamma s A :
  [ Gamma |- s :- A ] -> forall t, step s t -> [ Gamma |- t :- A ].
Proof.
  elim=> {Gamma s A}.
  - move=> Gamma x _ _ t st. by inv st.
  - move=> Gamma n _ t st. by inv st.
  - move=> Gamma A B s t u->{u} tp1 ih1 tp2 ih2 u st. inv st.
    + apply ty_lam_inv in tp1. eapply ty_subst1; by eauto.
    + eapply ty_app => //. eapply ih1=>//. by [].
    + case: (propagation tp1) => m /ty_prod_inv[_ tp3].
      eapply ty_conv. eapply ty_app. reflexivity. eassumption.
      apply: ih2 => //. apply: conv_beta. exact: conv1i.
      eapply ty_subst1; eauto. by autosubst.
  - move=> Gamma A B s n tp1 ih1 tp2 ih2 t st. inv st.
    apply: ty_lam. exact: ih2.
  - move=> Gamma A B n tp1 ih1 tp2 ih2 t st. inv st.
    + apply: ty_prod. exact: ih1. eapply (ty_ctx_conv tp2).
      exact: conv1i. by eapply ih1.
    + apply: ty_prod. exact: tp1. exact: ih2.
  - move=> Gamma s A B n tp1 ih1 con tp2 ih2 t st. apply: ty_conv con tp2.
    exact: ih1.
  - move=> Gamma s A B tp1 ih1 sb t st. apply: ty_sub sb. exact: ih1.
Qed.
