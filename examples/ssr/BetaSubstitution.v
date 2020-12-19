(** * Correctness of Single Variable Substitutions *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import Autosubst.Autosubst.

Set Implicit Arguments.
Unset Strict Implicit.

(** Untyped Lambda Terms and Parallel Substitutions *)

Inductive term :=
| Var (x : var)
| App (s t : term)
| Lam (s : {bind term}).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

(** The optimized implementation of single variable substitutions *)

Fixpoint lift_at (d k : nat) (s : term) : term :=
  match s with
    | Var i   => if i < d then Var i else Var (k + i)
    | App s t => App (lift_at d k s) (lift_at d k t)
    | Lam s   => Lam (lift_at d.+1 k s)
  end.
Notation lift := (lift_at 0).

Fixpoint sbst_at (d : nat) (t s : term) : term :=
  match s with
    | Var x => if x < d then Var x else if x == d then lift d t else Var x.-1
    | App s1 s2 => App (sbst_at d t s1) (sbst_at d t s2)
    | Lam s => Lam (sbst_at d.+1 t s)
  end.
Notation sbst := (sbst_at 0).

(** Soundness proof *)

Lemma lift_at_sound d k s :
  lift_at d k s = s.[upn d (ren (+k))].
Proof.
  elim: s d => /=[x|s ihs t iht|s ih] d.
  - elim: d x => //= d ih [|x] //. rewrite iterate_S; asimpl.
    by rewrite -ih (fun_if (subst (ren (+1)))).
  - by rewrite ihs iht.
  - by rewrite ih.
Qed.

Lemma lift_sound k s :
  lift k s = s.[ren (+k)].
Proof.
  exact: lift_at_sound.
Qed.

Lemma upnP n sigma x :
  upn n sigma x =
    if x < n then Var x else (sigma (x - n)).[ren (+n)].
Proof.
  case: ifPn.
  - elim: x n =>[|x ih][|n]//=/ih e. rewrite iterate_S. asimpl. by rewrite e.
  - rewrite -leqNgt. elim: x n => [|x ih][|n]; try autosubst. by case: n.
    move=>/ih e. rewrite iterate_S. asimpl. rewrite e. autosubst.
Qed.

Lemma sbst_at_sound d t s :
  sbst_at d t s = s.[upn d (t .: ids)].
Proof.
  elim: s d => /=[x|s1 ih1 s2 ih2|s ih] d.
  - rewrite lift_sound. rewrite upnP. case: ifPn => //=. rewrite -leqNgt => le.
    case: ifP => [/eqP->|/eqP/eqP]. by rewrite subnn. rewrite neq_ltn =>/orP[|{le}]//.
    move=> /leq_trans/(_ le). by rewrite ltnn. rewrite -subn_gt0 => p.
    move: (p) => /ltn_predK<-/=. rewrite/ids/Ids_term. f_equal.
    case: x p => //= n p. rewrite subSKn plusE subnKC //. by rewrite subn_gt0 in p.
  - by rewrite ih1 ih2.
  - by rewrite ih.
Qed.

Lemma sbst_sound t s :
  sbst t s = s.[t/].
Proof.
  exact: sbst_at_sound.
Qed.
