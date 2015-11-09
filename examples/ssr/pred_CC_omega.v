(** * Predicative CC omega: Type Preservation and Confluence
 *)

Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq.
Require Import AutosubstSsr ARS Context.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** **** Curry-style type theory with a hierarchy of predicative universes. *)

Inductive term : Type :=
| Var (x : var)
| Sort (n : nat)
| App  (s t : term)
| Lam  (s : {bind term})
| Prod (s : term) (t : {bind term}).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

(** **** One-Step Reduction *)

Inductive step : term -> term -> Prop :=
| step_beta s t u :
    u = s.[t/] -> step (App (Lam s) t) u
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

Lemma red_lam s1 s2 : red s1 s2 -> red (Lam s1) (Lam s2).
Proof. apply: star_hom => x y. exact: step_lam. Qed.

Lemma red_prod s1 s2 t1 t2 :
  red s1 s2 -> red t1 t2 -> red (Prod s1 t1) (Prod s2 t2).
Proof.
  move=> A B. apply: (star_trans (Prod s2 t1)).
  - apply: (star_hom (Prod^~ t1)) A => x y. exact: step_prodL.
  - apply: star_hom B => x y. exact: step_prodR.
Qed.

Lemma red_subst sigma s t : red s t -> red s.[sigma] t.[sigma].
Proof. apply: star_hom. exact: step_subst. Qed.

Lemma sred_up sigma tau : sred sigma tau -> sred (up sigma) (up tau).
Proof. move=> A [|n] //=. asimpl. apply: red_subst. exact: A. Qed.

Hint Resolve red_app red_lam red_prod sred_up : red_congr.

Lemma red_compat sigma tau s : sred sigma tau -> red s.[sigma] s.[tau].
Proof. elim: s sigma tau => *; asimpl; eauto with red_congr. Qed.

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

Lemma conv_lam s1 s2 : s1 === s2 -> Lam s1 === Lam s2.
Proof. apply: conv_hom => x y. exact: step_lam. Qed.

Lemma conv_prod s1 s2 t1 t2 :
  s1 === s2 -> t1 === t2 -> Prod s1 t1 === Prod s2 t2.
Proof.
  move=> A B. apply: (conv_trans (Prod s2 t1)).
  - apply: (conv_hom (Prod^~ t1)) A => x y. exact: step_prodL.
  - apply: conv_hom B => x y. exact: step_prodR.
Qed.

Lemma conv_subst sigma s t : s === t -> s.[sigma] === t.[sigma].
Proof. apply: conv_hom. exact: step_subst. Qed.

Lemma sconv_up sigma tau : sconv sigma tau -> sconv (up sigma) (up tau).
Proof. move=> A [|x] //=. asimpl. exact: conv_subst. Qed.

Lemma conv_compat sigma tau s :
  sconv sigma tau -> s.[sigma] === s.[tau].
Proof.
  elim: s sigma tau => *; asimpl; eauto using
    conv_app, conv_lam, conv_prod, sconv_up.
Qed.

Lemma conv_beta s t1 t2 : t1 === t2 -> s.[t1/] === s.[t2/].
Proof. move=> c. by apply: conv_compat => -[]. Qed.

(** **** Church-Rosser theorem *)

Inductive pstep : term -> term -> Prop :=
| pstep_beta s1 s2 t1 t2 u :
    u = s2.[t2/] ->
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
    | App (Lam s) t => (rho s).[rho t/]
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
  move=> A [|n] //=. asimpl. apply: pstep_subst. exact: A.
Qed.

Lemma pstep_compat sigma tau s t :
  psstep sigma tau -> pstep s t -> pstep s.[sigma] t.[tau].
Proof with eauto using pstep, psstep_up.
  move=> A B. elim: B sigma tau A; asimpl...
  move=> s1 s2 t1 t2 u -> _ A _ B sigma tau C.
  apply: (@pstep_beta _ (s2.[up tau]) _ (t2.[tau])); asimpl...
Qed.

Lemma pstep_compat_beta s1 s2 t1 t2 :
  pstep s1 s2 -> pstep t1 t2 -> pstep s1.[t1/] s2.[t2/].
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

Lemma inj_sort n m : Sort n === Sort m -> n = m.
Proof.
  move=> A. suff: (Sort n = Sort m) => [[//]|].
  eapply cr_conv_normal => //; done.
Qed.

Lemma inj_prod A1 A2 B1 B2 :
  Prod A1 B1 === Prod A2 B2 -> A1 === A2 /\ B1 === B2.
Proof.
  move=>/church_rosser[z /red_prod_inv s1 /red_prod_inv s2].
  inv s1; inv s2; split; eauto using join_conv.
Qed.

Lemma conv_prod_sort A B n :
  ~(Prod A B === Sort n).
Proof.
  move=> h. apply cr_star_normal in h => //. apply red_prod_inv in h. inv h.
Qed.

(** **** Cumulativity / Subtyping relation *)

Inductive sub1 : term ->term -> Prop :=
| sub1_refl A : sub1 A A
| sub1_sort n m : n <= m -> sub1 (Sort n) (Sort m)
| sub1_prod A B1 B2 : sub1 B1 B2 -> sub1 (Prod A B1) (Prod A B2).

CoInductive sub (A B : term) : Prop :=
| SubI A' B' : sub1 A' B' -> A === A' -> B' === B -> sub A B.
Infix "<:" := sub (at level 50, no associativity).

Lemma sub1_sub A B : sub1 A B -> sub A B. move=> /SubI. exact. Qed.
Lemma sub1_conv B A C : sub1 A B -> B === C -> A <: C. move=>/SubI. exact. Qed.
Lemma conv_sub1 B A C : A === B -> sub1 B C -> A <: C. move=>c/SubI. exact. Qed.

Lemma conv_sub A B : A === B -> A <: B.
Proof. move/conv_sub1. apply. exact: sub1_refl. Qed.

Lemma sub_refl A : A <: A.
Proof. apply: sub1_sub. exact: sub1_refl. Qed.
Hint Resolve sub_refl.

Lemma sub_sort n m : n <= m -> Sort n <: Sort m.
Proof. move=> leq. exact/sub1_sub/sub1_sort. Qed.

Lemma sub1_trans A B C D :
  sub1 A B -> B === C -> sub1 C D -> A <: D.
Proof with eauto using sub1, sub1_sub, sub1_conv, conv_sub1.
  move=> sb. elim: sb C D => {A B}
    [A C D|n m leq C D conv sb|A B1 B2 sb1 ih C D conv sb2]...
  - inv sb...
    + apply: sub_sort. move: conv => /inj_sort eqn. subst.
      exact: leq_trans leq _.
    + exfalso. exact: conv_prod_sort (conv_sym conv).
  - inv sb2...
    + exfalso. exact: conv_prod_sort conv.
    + move: conv => /inj_prod[conv1 conv2].
      move: (ih _ _ conv2 H) => {ih} sub. inv sub.
      eapply SubI. eapply sub1_prod... eapply conv_prod... exact: conv_prod.
Qed.

Lemma sub_trans B A C :
  A <: B -> B <: C -> A <: C.
Proof.
  move=> [A' B' s1 c1 c2] [B'' C' s2 c3 c4]. move: (conv_trans _ c2 c3) => h.
  case: (sub1_trans s1 h s2) => A0 B0 s3 c5 c6. apply: (SubI s3).
  exact: conv_trans c5. exact: conv_trans c4.
Qed.

Lemma sub_prod_inv A1 A2 B1 B2 :
  Prod A1 B1 <: Prod A2 B2 -> A1 === A2 /\ B1 <: B2.
Proof.
  move=> [A' B' []].
  - move=> C c1 c2. have{c1 c2}/inj_prod[c1 c2]: Prod A1 B1 === Prod A2 B2.
     exact: conv_trans c2.
    split=>//. exact: conv_sub.
  - by move=> n _ _ /conv_prod_sort[].
  - move=> A C1 C2 sb /inj_prod[c1 c2] /inj_prod[c3 c4]. split.
    exact: conv_trans c3. exact: SubI sb c2 c4.
Qed.

Lemma sub1_subst sigma A B : sub1 A B -> sub1 A.[sigma] B.[sigma].
Proof. move=> s. elim: s sigma => /=; eauto using sub1. Qed.

Lemma sub_subst sigma A B : A <: B -> A.[sigma] <: B.[sigma].
Proof. move=> [A' B' /sub1_subst]; eauto using sub, conv_subst. Qed.

(** **** Typing *)

Notation "Gamma `_ i" := (dget Gamma i).

Reserved Notation "[ Gamma |- ]".
Reserved Notation "[ Gamma |- s :- A ]".

Inductive has_type : list term -> term -> term -> Prop :=
| ty_var Gamma x :
    x < size Gamma ->
    [ Gamma |- Var x :- Gamma`_x ]
| ty_sort Gamma n  :
    [ Gamma |- Sort n :- Sort n.+1 ]
| ty_app Gamma A B s t :
    [ Gamma |- s :- Prod A B ] ->
    [ Gamma |- t :- A ] ->
    [ Gamma |- App s t :- B.[t/] ]
| ty_lam Gamma A B s n :
    [ Gamma |- A :- Sort n ] ->
    [ A :: Gamma |- s :- B ] ->
    [ Gamma |- Lam s :- Prod A B ]
| ty_prod Gamma A B n :
    [ Gamma |- A :- Sort n ] ->
    [ A :: Gamma |- B :- Sort n ] ->
    [ Gamma |- Prod A B :- Sort n ]
| ty_sub Gamma n A B s :
    A <: B ->
    [ Gamma |- B :- Sort n ] ->
    [ Gamma |- s :- A ] ->
    [ Gamma |- s :- B ]
where "[ Gamma |- s :- A ]" := (has_type Gamma s A).

Inductive context_ok : list term -> Prop :=
| ctx_nil :
    [ [::] |- ]
| ctx_ncons Gamma A n :
    [ Gamma |- A :- Sort n ] ->
    [ Gamma |- ] ->
    [ A :: Gamma |- ]
where "[ Gamma |- ]" := (context_ok Gamma).

Lemma ty_evar Gamma (A : term) (x : var) :
  A = Gamma`_x -> x < size Gamma -> [ Gamma |- Var x :- A ].
Proof. move->. exact: ty_var. Qed.

Lemma ty_eapp Gamma (A B C s t : term) :
  C = B.[t/] ->
  [ Gamma |- s :- Prod A B ] -> [ Gamma |- t :- A ] ->
  [ Gamma |- App s t :- C ].
Proof. move=>->. exact: ty_app. Qed.

(* Type well-formedness *)

Notation "[ Gamma |- s ]" := (exists n, [ Gamma |- s :- Sort n ]).

Lemma ty_sort_wf Gamma n : [ Gamma |- Sort n ].
Proof. exists n.+1. exact: ty_sort. Qed.
Hint Resolve ty_sort_wf ty_sort.

Lemma ty_prod_wf Gamma A B :
  [ Gamma |- A ] -> [ A :: Gamma |- B ] -> [ Gamma |- Prod A B ].
Proof.
  move=> [n tp1] [m tp2]. exists (maxn n m). apply: ty_prod.
  - eapply (ty_sub (A := Sort n)); eauto. eapply sub_sort. exact: leq_maxl.
  - eapply (ty_sub (A := Sort m)); eauto. apply: sub_sort. exact: leq_maxr.
Qed.

(* Substitution Lemma *)

Notation "[ Delta |- sigma -| Gamma ]" :=
  (forall x, x < size Gamma -> [ Delta |- sigma x :- (Gamma`_x).[sigma] ]).

Lemma ty_renaming xi Gamma Delta s A :
  [ Gamma |- s :- A ] ->
  (forall x, x < size Gamma -> xi x < size Delta) ->
  (forall x, x < size Gamma -> (Gamma`_x).[ren xi] = Delta`_(xi x)) ->
  [ Delta |- s.[ren xi] :- A.[ren xi] ].
Proof.
  move=> tp. elim: tp xi Delta => {Gamma s A} /=
    [Gamma x si|Gamma n|Gamma A B s t _ ih1 _ ih2|
     Gamma A B s n _ ih1 _ ih2|Gamma A B n _ ih1 _ ih2|
     Gamma n A B s sub _ ih1 _ ih2]
    xi Delta subctx eqn //=.
  - rewrite eqn //. apply: ty_var. exact: subctx.
  - apply: (@ty_eapp _ A.[ren xi] B.[up (ren xi)]). autosubst.
      exact: ih1. exact: ih2.
  - eapply ty_lam. by eapply ih1. asimpl. apply: ih2.
    + by move=> [//|x /subctx].
    + by move=> [_|x /eqn/=<-]; autosubst.
  - apply: ty_prod. exact: ih1. asimpl. apply: ih2.
    + by move=> [//|x /subctx].
    + by move=> [_|x /eqn/=<-]; autosubst.
  - apply: (@ty_sub _ n A.[ren xi] B.[ren xi]). exact: sub_subst.
      exact: ih1. exact: ih2.
Qed.

Lemma weakening Gamma s A B :
  [ Gamma |- s :- A ] -> [ B :: Gamma |- s.[ren (+1)] :- A.[ren (+1)] ].
Proof. move=> /ty_renaming. exact. Qed.

Lemma eweakening Gamma s s' A A' B :
  s' = s.[ren (+1)] -> A' = A.[ren (+1)] ->
  [ Gamma |- s :- A ] -> [ B :: Gamma |- s' :- A' ].
Proof. move=>->->. exact: weakening. Qed.

Lemma ty_ok Gamma :
  [ Gamma |- ] -> forall x, x < size Gamma -> [ Gamma |- Gamma`_x ].
Proof.
  elim=> // {Gamma} Gamma A n tp _ ih [_|x /ih [{n tp} n tp]];
    exists n; exact: weakening tp.
Qed.

Lemma sty_up sigma Gamma Delta A :
  [ Delta |- sigma -| Gamma ] ->
  [ A.[sigma] :: Delta |- up sigma -| A :: Gamma ].
Proof.
  move=> stp [_//|x /stp tp] /=. apply: ty_evar => //=. autosubst.
  apply: eweakening tp; autosubst.
Qed.

Lemma ty_subst sigma Gamma Delta s A :
  [ Delta |- sigma -| Gamma ] -> [ Gamma |- s :- A ] ->
  [ Delta |- s.[sigma] :- A.[sigma] ].
Proof.
  move=> stp tp. elim: tp sigma Delta stp => {Gamma s A} /=
    [Gamma x si|Gamma n|Gamma A B s t _ ih1 _ ih2|
     Gamma A B s n _ ih1 _ ih2|Gamma A B n _ ih1 _ ih2|
     Gamma n A B s sub _ ih1 _ ih2] sigma Delta stp //=.
  - exact: stp.
  - apply: (@ty_eapp _ A.[sigma] B.[up sigma]). autosubst.
      exact: ih1. exact: ih2.
  - eapply ty_lam. by eapply ih1. apply: ih2. exact: sty_up.
  - apply: ty_prod. exact: ih1. apply ih2. exact: sty_up.
  - apply: (@ty_sub _ n A.[sigma] B.[sigma]). exact: sub_subst.
      exact: ih1. exact: ih2.
Qed.

Lemma ty_cut Gamma s t A B :
  [ A :: Gamma |- s :- B ] -> [ Gamma |- t :- A ] ->
  [ Gamma |- s.[t/] :- B.[t/] ].
Proof.
  move=> /ty_subst h tp. apply: h => -[_|x leq]; asimpl => //. exact: ty_var.
Qed.

Lemma ty_ctx_conv Gamma s A B C n :
  [ A :: Gamma |- s :- C ] -> B === A -> [ Gamma |- A :- Sort n ] ->
  [ B :: Gamma |- s :- C ].
Proof.
  move=> tp1 conv tp2. cut ([ B :: Gamma |- s.[ids] :- C.[ids] ]). autosubst.
  apply: ty_subst tp1. move=> [_|x //=]. asimpl. eapply ty_sub.
  eapply conv_sub. eapply (conv_subst _ conv).
  apply: eweakening tp2 => //. eapply ty_var => //.
  move=> le. asimpl. exact: ty_var.
Qed.

(* Inversion Lemmas *)

Lemma ty_prod_invX Gamma A B n u :
  [ Gamma |- Prod A B :- u ] -> u <: Sort n ->
    [ Gamma |- A :- Sort n ] /\ [ A :: Gamma |- B :- Sort n ].
Proof.
  move e:(Prod A B) => s tp. elim: tp A B e n => //{Gamma s u}
    [Gamma A B n tp1 _ tp2 _ A' B' [->->]
    |Gamma n s A B sub1 _ _ tp ih A' B' e] m sub2.
  - eauto using ty_sub.
  - subst. apply: ih => //. exact: sub_trans sub1 sub2.
Qed.

Lemma ty_prod_inv Gamma A B n :
  [ Gamma |- Prod A B :- Sort n ] ->
    [ Gamma |- A :- Sort n ] /\ [ A :: Gamma |- B :- Sort n ].
Proof. move=> h. exact: (ty_prod_invX h). Qed.

Lemma ty_lam_invX Gamma s A B C :
  [ Gamma |- Lam s :- C ] ->
  (C <: Prod A B /\ [ A :: Gamma |- B ]) \/ Prod A B = C ->
  [ A :: Gamma |- s :- B ].
Proof.
  move e:(Lam s) => t tp. elim: tp A B s e => // {Gamma t C}.
  - move=> Gamma A B s n tp1 _ tp2 _ A' B' s' [->] [|[->->//]].
    move=> [/sub_prod_inv[con sub] [m tp3]]. apply: ty_sub sub tp3 _.
    apply: ty_ctx_conv tp2 _ tp1. exact: conv_sym.
  - move=>Gamma n A B s sub1 tp1 ih1 tp2 ih2 A' B' t eqn1 [[sub2 [m tp3]]|eqn2];
      subst; apply: ih2 => //; left; split => //.
    + exact: sub_trans sub1 sub2. by exists m.
    + exists n. by move: tp1 => /ty_prod_inv[].
Qed.

Lemma ty_lam_inv Gamma s A B :
  [ Gamma |- Lam s :- Prod A B ] -> [ A :: Gamma |- s :- B ].
Proof. move=> tp. apply: ty_lam_invX tp _. by right. Qed.

(* Main Result *)

Lemma propagation Gamma s A :
  [ Gamma |- s :- A ] -> [ Gamma |- ] -> [ Gamma |- A ].
Proof.
  elim=> {Gamma s A} /=
    [Gamma x si /ty_ok||Gamma A B _ t _ ih tp _ ok|Gamma A B s n tp _ _ ih ok|
    |Gamma n A B s _ tp _ _ _ _] //.
  - exact.
  - move: (ih ok) => [n {ih ok} /ty_prod_inv[_ ih]].
    exists n. exact: ty_cut ih tp.
  - apply: ty_prod_wf. by exists n. apply: ih. exact: ctx_ncons tp ok.
  - by exists n.
Qed.

Lemma subject_reduction Gamma s A :
  [ Gamma |- ] -> [ Gamma |- s :- A ] ->
    forall t, step s t -> [ Gamma |- t :- A ].
Proof.
  move=> wf tp. elim: tp wf => {Gamma s A}.
  - move=> Gamma x _ wf t st. by inv st.
  - move=> Gamma n wf t st. by inv st.
  - move=> Gamma A B s t tp1 ih1 tp2 ih2 wf u st. inv st.
    + apply ty_lam_inv in tp1. exact: ty_cut tp1 tp2.
    + apply: ty_app tp2. exact: ih1.
    + move: (tp1) => /propagation/(_ wf)[m]/ty_prod_inv[_ tp3].
      eapply ty_sub; last first. eapply ty_app. eassumption. exact: ih2.
      move: (ty_cut tp3 tp2) => /= h. apply h. apply: conv_sub.
      apply: conv_beta. exact: conv1i.
  - move=> Gamma A B s n tp1 ih1 tp2 ih2 wf t st. inv st.
    apply: ty_lam (tp1) _. apply: ih2 => //. apply: ctx_ncons tp1 wf.
  - move=> Gamma A B n tp1 ih1 tp2 ih2 wf t st. inv st.
    + apply: ty_prod. exact: ih1. eapply (ty_ctx_conv tp2).
      exact: conv1i. eassumption.
    + apply: ty_prod => //. apply: ih2 => //. exact: ctx_ncons tp1 wf.
  - move=> Gamma s A B n tp1 ih1 con tp2 ih2 wf t st.
    apply: ty_sub tp1 ih1 _. exact: ih2.
Qed.

(* Local Variables: *)
(* coq-load-path: (("." "Ssr")) *)
(* End: *)
