Require Import Omega Autosubst.MMap List Program.Equality.
Require Import Autosubst.Lib Autosubst.Autosubst.

Fixpoint atn {X} l n (x : X) := 
  match l with 
    | nil => False
    | y :: l' => match n with 
                  | 0 => x = y 
                  | S n' => atn l' n' x
                end
  end.


Section SubstInstance.


Context {term : Type}.
Context {VarConstr_term : VarConstr term} {Rename_term : Rename term} {Subst_term : Subst term}.
Context {subst_lemmas : SubstLemmas term}.

Inductive atnd: list term -> var -> term -> Prop :=
| Atnd0 Delta A A': A' = A.[ren(+1)] -> atnd (A :: Delta) 0 A'
| AtndS Delta x A B B' : atnd Delta x B -> B' = B.[ren(+1)] -> atnd (A :: Delta) (S x) B'
.

Lemma atn_mmap {f : term -> term} {Gamma x A A'} : atn Gamma x A -> A' = (f A) -> atn (mmap f Gamma) x A'.
Proof.
  revert x.
  induction Gamma; intros; simpl in *; trivial.
  destruct x; subst; eauto.
Qed.

Lemma mmap_atn {f : term -> term} {Gamma x A'} : atn (mmap f Gamma) x A' -> exists A, A' = (f A) /\ atn Gamma x A.
Proof.
  revert x. induction Gamma; intros; simpl in *. 
  - contradiction.
  - destruct x; subst; eauto.
Qed.

Lemma up_mmap_atn zeta xi Gamma1 Gamma2 A x: 
  (forall x B, atn Gamma1 x B -> atn Gamma2 (zeta x) B.[ren xi]) ->
  atn (mmap (subst (ren (+1))) Gamma1) x A ->
  atn (mmap (subst (ren (+1))) Gamma2) (zeta x) A.[ren (0 .: xi >> (+1))].
Proof.
  intros H1 H2. 
  edestruct (mmap_atn H2) as [? [? ?]]. subst.
  eapply atn_mmap; eauto. now autosubst.
Qed.

Lemma up_atnd xi Delta1 Delta2 A B x:
  (forall x C, atnd Delta1 x C -> atnd Delta2 (xi x) C.[ren xi]) ->
  atnd (A :: Delta1) x B ->
  atnd (A.[ren xi] :: Delta2) ((0 .: xi >> (+1)) x) B.[ren (0 .: xi >> (+1))].
Proof.
  intros H1 H2; destruct x; autosubst; inv H2; econstructor; eauto; now autosubst.
Qed.


Lemma atnd_steps x Gamma Delta A : atnd Gamma x A <-> atnd (Delta ++ Gamma) (length Delta + x) A.[ren(+(length Delta))].
Proof.
  revert A x.
  induction Delta; intros.
  - split. 
    + now autosubst.
    + now autosubst.
  - simpl. cutrewrite (A.[ren (+S (length Delta))] = A.[ren(+length Delta)].[ren(+1)]); [idtac | now autosubst].
    split.
      + econstructor. eapply IHDelta; eassumption. reflexivity.
      + intros H. inv H. rewrite IHDelta. apply lift_inj in H5. subst. eassumption.
Qed.

Lemma atnd_steps' x Gamma Delta A :  atnd (Delta ++ Gamma) (x + length Delta) A ->
                               exists B, A = B.[ren(+(length Delta))] /\ atnd Gamma x B.
Proof.
  revert A x.
  induction Delta; intros.
  - exists A.
    simpl in H.
    rewrite plus_0_r in H. autosubst.
    intuition. 
  - autosubst. simpl in *.
    rewrite NPeano.Nat.add_succ_r in *.
    inv H.
    edestruct IHDelta as [B' [? ?]]; eauto. exists B'. subst.
    autosubst. intuition.
Qed.

Corollary atnd_step Delta A x B : atnd Delta x A <-> atnd (B :: Delta) (S x) A.[ren(+1)].
Proof.
  apply atnd_steps with (Delta := B :: nil).
Qed.

Lemma atnd_repl Gamma A Delta : 
  (atnd (Delta ++ A :: Gamma) (length Delta) A.[ren(+ S (length Delta))]) /\
  (forall x B A', x <> length Delta -> atnd (Delta ++ A :: Gamma) x B -> atnd (Delta ++ A' :: Gamma) x B).
Proof.
  split.
  - pose proof (atnd_steps 0 (A :: Gamma) Delta A.[ren(+1)]) as H.
    rewrite plus_0_r in H.
    cutrewrite (A.[ren (+1)].[ren (+length Delta)] =  A.[ren (+S (length Delta))]) in H. { apply H. now constructor. }
    now autosubst.
  - intros x. revert Gamma A Delta.
    induction x; intros Gamma A Delta H B A' H_atn.
    + destruct Delta as [| C Delta]. { now intuition. }
      simpl in *.
      inv H_atn. now constructor. 
    + destruct Delta as [| C Delta]; simpl in *. 
      * inv H_atn. econstructor. eassumption. reflexivity.
      * inv H_atn. econstructor. eapply IHx; eauto. reflexivity.
Qed.

Lemma atnd_defined Delta x : (exists B, atnd Delta x B) <-> x < length Delta.
Proof.
  revert x. induction Delta; intuition; autosubst in *; ainv.
  - destruct x. omega. cut(x < length Delta). omega.
    ainv. firstorder.
  - destruct x. 
    + eexists. now econstructor. 
    + edestruct IHDelta as [_ [? ?]]. cut(x < length Delta); eauto. omega.
      eexists. econstructor; eauto.
Qed.

End SubstInstance.