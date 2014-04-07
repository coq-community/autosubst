
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope prop_scope with PROP.
Open Scope prop_scope.

Notation "e1 <=2 e2" := (forall x y, e1 x y -> e2 x y)
  (at level 70, no associativity) : prop_scope.
Notation "e1 <=>2 e2" := (e1 <=2 e2 /\ e2 <=2 e1)
  (at level 70, no associativity) : prop_scope.

Definition Pred (T : Type) := T -> Prop.
Definition Rel  (T : Type) := T -> Pred T.

Section Definitions.

Variables (T : Type) (e : Rel T).
Implicit Types (R S : T -> T -> Prop).

Inductive star (x : T) : T -> Prop :=
| starR : star x x
| starSE y z : star x y -> e y z -> star x z.

Inductive conv (x : T) : T -> Prop :=
| convR : conv x x
| convSE y z : conv x y -> e y z -> conv x z
| convSEi y z : conv x y -> e z y -> conv x z.

Definition com R S := forall x y z, R x y -> S x z -> exists2 u, S y u & R z u.

Definition joinable R x y := exists2 z, R x z & R y z.
Definition diamond := forall x y z, e x y -> e x z -> exists2 u, e y u & e z u.
Definition confluent := forall x y z, star x y -> star x z -> joinable star y z.
Definition CR := forall x y, conv x y -> joinable star x y.

Hint Resolve starR convR.

Lemma star1 x y : e x y -> star x y.
Proof. exact: starSE. Qed.

Lemma star_trans y x z : star x y -> star y z -> star x z.
Proof. move=> A. elim=> //={z} y' z _. exact: starSE. Qed.

Lemma starES x y z : e x y -> star y z -> star x z.
Proof. move/star1. exact: star_trans. Qed.

Lemma star_conv x y : star x y -> conv x y.
Proof. elim=> //={y} y z _. exact: convSE. Qed.

Lemma conv1 x y : e x y -> conv x y.
Proof. exact: convSE. Qed.

Lemma conv1i x y : e y x -> conv x y.
Proof. exact: convSEi. Qed.

Lemma conv_trans y x z : conv x y -> conv y z -> conv x z.
Proof. move=> A. elim=> //={z} y' z _. exact: convSE. exact: convSEi. Qed.

Lemma convES x y z : e x y -> conv y z -> conv x z.
Proof. move/conv1. exact: conv_trans. Qed.

Lemma convESi x y z : e y x -> conv y z -> conv x z.
Proof. move/conv1i. exact: conv_trans. Qed.

Lemma conv_sym x y : conv x y -> conv y x.
Proof. elim=> //={y} y z _ ih h; [exact: convESi ih|exact: convES ih]. Qed.

Lemma join_conv x y z : star x y -> star z y -> conv x z.
Proof.
  move=> sxy szy. apply: (@conv_trans y); [|apply: conv_sym]; exact: star_conv.
Qed.

Lemma confluent_cr :
  confluent <-> CR.
Proof.
  split=> [h x y|h x y z /star_conv A /star_conv B].
  - elim=> [|{y} y z _ [u h1 h2] /star1 h3|{y} y z _ [u h1 h2] h3].
    + by exists x.
    + case: (h y u z h2 h3) => v {h2 h3} h2 h3.
      exists v => //. exact: star_trans h2.
    + exists u => //. exact: starES h2.
  - apply: h. apply: conv_trans B. exact: conv_sym.
Qed.

End Definitions.

Hint Resolve starR convR.
Arguments star_trans {T e} y {x z} A B.
Arguments conv_trans {T e} y {x z} A B.

Lemma star_img T1 T2 (f : T1 -> T2) (e1 : Rel T1) e2 :
  (forall x y, e1 x y -> star e2 (f x) (f y)) ->
  (forall x y, star e1 x y -> star e2 (f x) (f y)).
Proof.
  move=> A x y. elim=> //=y' z _ B /A. exact: star_trans.
Qed.

Lemma star_hom T1 T2 (f : T1 -> T2) (e1 : Rel T1) (e2 : Rel T2) :
  (forall x y, e1 x y -> e2 (f x) (f y)) ->
  (forall x y, star e1 x y -> star e2 (f x) (f y)).
Proof.
  move=> A. apply: star_img => x y /A. exact: star1.
Qed.

Lemma conv_img T1 T2 (f : T1 -> T2) (e1 : Rel T1) e2 :
  (forall x y, e1 x y -> conv e2 (f x) (f y)) ->
  (forall x y, conv e1 x y -> conv e2 (f x) (f y)).
Proof.
  move=> A x y. elim=> //=y' z _ B /A. exact: conv_trans.
  move=> C. apply: conv_trans B _. exact: conv_sym.
Qed.

Lemma conv_hom T1 T2 (f : T1 -> T2) (e1 : Rel T1) (e2 : Rel T2) :
  (forall x y, e1 x y -> e2 (f x) (f y)) ->
  (forall x y, conv e1 x y -> conv e2 (f x) (f y)).
Proof.
  move=> A. apply: conv_img => x y /A. exact: conv1.
Qed.

Arguments star_img {T1 T2} f e1 {e2} A x y B.
Arguments star_hom {T1 T2} f e1 {e2} A x y B.
Arguments conv_img {T1 T2} f e1 {e2} A x y B.
Arguments conv_hom {T1 T2} f e1 {e2} A x y B.

Lemma star_closure T (e1 e2 : Rel T) : e1 <=2 star e2 -> star e1 <=2 star e2.
Proof. exact: star_img. Qed.

Lemma star_monotone T (e1 e2 : Rel T) : e1 <=2 e2 -> star e1 <=2 star e2.
Proof. move=> A. apply: star_closure => x y /A. exact: star1. Qed.

Lemma eq_star T (e1 e2 : Rel T) :
  e1 <=2 star e2 -> e2 <=2 star e1 -> star e1 <=>2 star e2.
Proof. move=> A B. split; exact: star_closure. Qed.

Lemma star_interpolation T (e1 e2 : Rel T) :
  e1 <=2 e2 -> e2 <=2 star e1 -> star e1 <=>2 star e2.
Proof. move=> A B. apply: eq_star => // x y /A. exact: star1. Qed.

Lemma confluent_stable T (e1 e2 : Rel T) :
  star e1 <=>2 star e2 -> confluent e1 -> confluent e2.
Proof.
  move=>[A B] C x y z /B exy /B exz. case: (C _ _ _ exy exz) => u /A eyu /A ezu.
  by exists u.
Qed.

Lemma conv_closure T (e1 e2 : Rel T) : e1 <=2 conv e2 -> conv e1 <=2 conv e2.
Proof.
  move=> A x y. elim=> //=y' z _ B /A. exact: conv_trans.
  move=> C. apply: conv_trans B _. exact: conv_sym.
Qed.

Section Commutation.
Variable T : Type.

Lemma com_strip (e1 e2 : Rel T) : com e1 e2 -> com (star e2) e1.
Proof.
  move=> A x y z. elim=> {y} [B|y w C ih eyw /ih[u eyu s]]. by exists z.
  case: (A _ _ _ eyu eyw) => v euv ewv. exists v => //. exact: starSE euv.
Qed.

Lemma com_lift (e1 e2 : Rel T) : com e1 e2 -> com (star e1) (star e2).
Proof. by move/com_strip/com_strip. Qed.

Corollary diamond_confluent (e : Rel T) : diamond e -> confluent e.
Proof. exact: com_lift. Qed.

End Commutation.

Section Termination.
Variables (T : Type) (e : Rel T).

Definition reducible x := exists y, e x y.
Definition normal x := ~ reducible x.

Definition nf x y := star e x y /\ normal y.
Definition wn x := exists y, nf x y.

Inductive sn x : Prop :=
| SNI : (forall y, e x y -> sn y) -> sn x.

Lemma normal_star x y : star e x y -> normal x -> x = y.
Proof. move=> A B. elim: A => // y' z _ <- A. case: B. by exists z. Qed.

Hypothesis cr : CR e.

Lemma cr_star_normal x y : conv e x y -> normal y -> star e x y.
Proof. move=> /cr[z A B] C. by rewrite (normal_star B C). Qed.

Lemma cr_conv_normal x y : conv e x y -> normal x -> normal y -> x = y.
Proof. by move=> /cr[z A B] /(normal_star A)->/(normal_star B)->. Qed.

End Termination.

Section CoFinal.
Variables (T : Type) (e : Rel T) (rho : T -> T).

Definition normalizing :=
  forall x y, nf e x y -> exists n, y = iter n rho x.

Definition cofinal :=
  forall x y, star e x y -> exists n, star e y (iter n rho x).

Lemma cofinal_normalizing : cofinal -> normalizing.
Proof. move=> A x y [/A[n B] C]. exists n. exact: normal_star C. Qed.

Definition triangle := forall x y, e x y -> e y (rho x).

Lemma triangle_diamond : triangle -> diamond e.
Proof. move=> A x y z exy exz. exists (rho x); exact: A. Qed.

Hypothesis tri : triangle.

Lemma triangle_monotone x y : e x y -> e (rho x) (rho y).
Proof. by move/tri/tri. Qed.

Lemma triangle_cofinal : cofinal.
Proof.
  move=> x y. elim=> //=[|y' z A [n ih] B]. by exists 0.
  exists n.+1. apply: starES (tri B) _. rewrite iterS.
  apply: star_img ih => a b /triangle_monotone. exact: star1.
Qed.

End CoFinal.

(* The Tait, Martin-Loef, Takahashi confluence proof method. *)
Lemma cr_method T (e1 e2 : Rel T) (rho : T -> T) :
  e1 <=2 e2 -> e2 <=2 star e1 -> triangle e2 rho -> CR e1.
Proof.
  move=> A B C. apply confluent_cr.
  have[D1 D2]: star e1 <=>2 star e2. exact: star_interpolation.
  have: confluent e2. apply: diamond_confluent. exact: triangle_diamond C.
  exact: confluent_stable.
Qed.

(* Computing normal forms *)

Section ComputationN.
Variables (T : Type) (e : Rel T) (rho : T -> T).
Hypothesis norm : normalizing e rho.
Hypothesis sound : forall x, star e x (rho x).
Hypothesis classical : forall x, {reducible e x} + {normal e x}.

Inductive accn (x : T) : Prop :=
| accnH : normal e x -> accn x
| accnL : accn (rho x) -> accn x.
Scheme accn_ind' := Induction for accn Sort Prop.

Lemma nf_accn x y : nf e x y -> accn x.
Proof.
  move=> A. case: (norm A) => n. case: A => _. move/accnH.
  elim: n y => [|n ih] y A /= B. by rewrite -B.
  apply: (ih (iter n rho x)) => //. apply: accnL. by rewrite -B.
Qed.

Lemma wn_accn x : wn e x -> accn x.
Proof.
  move=> [y]. exact: nf_accn.
Qed.

Lemma sn_wn x : sn e x -> wn e x.
Proof.
  elim=> {x} x _ ih. case (classical x) => [[y exy]|A].
  - case: (ih _ exy) => z [A B]. exists z. split=> //. exact: starES A.
  - exists x. by split.
Qed.

Lemma accn_inv x (H1 : accn x) (H2 : reducible e x) : accn (rho x).
Proof. by case: H1. Defined.

Fixpoint evaln x (H : accn x) : T :=
  match classical x with
    | left a => evaln (accn_inv H a)
    | right _ => x
  end.

Lemma evaln_sound x (H : accn x) : nf e x (evaln H).
Proof.
  move: x H. apply: accn_ind'.
  - move=> x n /=. by case: (classical x).
  - move=> x a [A B] /=. case: (classical x) => //= _.
    split=>//. apply: star_trans A. exact: sound.
Qed.

Theorem evalnP x : ex (nf e x) -> sig (nf e x).
Proof.
  move=> A. exists (evaln (wn_accn A)). exact: evaln_sound.
Qed.

End ComputationN.