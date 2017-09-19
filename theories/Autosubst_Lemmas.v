(** Some useful lemmas about substitutions. *)
Require Import Autosubst_Basics Autosubst_MMap Autosubst_Classes Autosubst_Tactics.

Section SubstLemmas.

Context {term : Type} {Ids_term : Ids term}
  {Rename_term : Rename term} {Subst_term : Subst term}
  {SubstLemmas_term : SubstLemmas term}.

Lemma up_id : up ids = ids.
Proof. autosubst. Qed.

Lemma up_id_n n : upn n ids = ids.
Proof. induction n; [reflexivity|rewrite !iterate_S, IHn]. exact up_id. Qed.

Lemma lift0 : ren (+0) = ids. autosubst. Qed.

Lemma up_lift1 sigma : ren (+1) >> up sigma = sigma >> ren (+1).
Proof. autosubst. Qed.

Lemma up_liftn sigma n : ren (+n) >> upn n sigma = sigma >> ren (+n).
Proof.
  f_ext. intros x. simpl. rewrite id_subst. induction n.
  - autosubst.
  - rewrite !iterate_S, upE. simpl. rewrite IHn. autosubst.
Qed.

Lemma up_comp sigma tau : up sigma >> up tau = up (sigma >> tau).
Proof. autosubst. Qed.

Lemma up_comp_n sigma tau n :
  upn n sigma >> upn n tau = upn n (sigma >> tau).
Proof. induction n; [reflexivity|now rewrite !iterate_S, <- IHn, up_comp]. Qed.

Lemma upn_upn i j sigma : upn i (upn j sigma) = upn (i + j) sigma.
Proof. eapply iterate_iterate. Qed.

Lemma ren_uncomp A xi zeta : A.[ren (xi >>> zeta)] = A.[ren xi].[ren zeta].
Proof. autosubst. Qed.

Lemma renS s n : s.[ren (+S n)] = s.[ren (+n)].[ren (+1)].
Proof. autosubst. Qed.

Lemma lift_inj (A B : term) : A.[ren(+1)] = B.[ren(+1)] -> A = B.
Proof.
  intros H. apply (f_equal (subst (ren pred))) in H. asimpl in H.
  unfold funcomp, lift in H. now asimpl in H.
Qed.

Lemma lift_injn (A B : term) n : A.[ren(+n)] = B.[ren(+n)] -> A = B.
Proof.
  induction n. autosubst. rewrite (@renS A), (@renS B).
  intros H. apply lift_inj in H. auto.
Qed.

Lemma lift_injn_eq (A B : term) n : A.[ren(+n)] = B.[ren(+n)] <-> A = B.
Proof.
  split; intros; subst; eauto using lift_injn.
Qed.

End SubstLemmas.

(* Local Variables: *)
(* coq-load-path: (("." "Autosubst")) *)
(* End: *)
