(** * Autosubst Tutorial

    In this tutorial we will use Autosubst to formalize the reduction relation
    of the untyped lambda calculus and show substitutivity. *)

Require Import Autosubst.

(** ** Syntax and the substitution operation

    The syntax of the untyped lambda calculus is given by the following grammar.
    #\[ s, t := x \mid s \, t \mid \lambda s \]#
    
    To generate the substitution operation we need an inductive type
    corresponding to the terms above with a few annotations.

    - There must be _exactly_ one variable constructor which has a single
      argument of type [var]. The type [var] is convertible to [nat], which is
      used to represent de Bruijn indices.
    - Subterms with additional bound variables must be of type [{bind term}]
      instead of [term]. The notation [{bind T}] is convertible to [T]. *)

Inductive term :=
| Var (x : var)
| App (s t : term)
| Lam (s : {bind term}).

(** Now we can automatically derive the substitution operations and lemmas.
    This is done by generating instances for the following typeclasses:

    - [Ids term] provides the generic identity substitution ids for term.
      It is always equivalent to the variable constructor of term, i.e.
      to the unique constructor having a single argument of type [var].
      In this example, [ids] is convertible to [Var].
    - [Rename term] provides the renaming operation on term.
    - [Subst term] provides the substitution operation on term and needs a
      [Rename] instance in the presence of binders.
    - [SubstLemmas term] contains proofs for the basic lemmas.

    Each instance is inferred automatically by using the [derive] tactic. *)

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

(** At this point we can use the notations:

    - [s.[sigma]] for the application of the substitution [sigma] to a term [s].
    - [sigma >> tau] for the composition of sigma and tau, i.e., the
      substitution [fun x => (sigma x).[tau]].

    Additionally there is a generic cast [ren] from renamings (functions of type
    [nat -> nat] to substitutions). Use [autosubst] to simplify terms containing
    substitutions. *)

(** ** Reduction and substitutivity

    The single-step reduction relation is defined by the following inference
    rules
    #\[ \cfrac{}{(\lambda s)\, t \rhd s.[t\cdot \text{id}]} \quad
        \cfrac{s_1 \rhd s_2}{s_1 \, t \rhd s_2 \, t} \quad 
        \cfrac{t_1 \rhd t_2}{s \, t_1 \rhd s \, t_2} \quad
        \cfrac{s_1 \rhd s_2}{\lambda s_1 \rhd \lambda s_2} \quad
    \]#

    The Coq notation for stream cons is [.:] and the identity substitution is
    [Var]. Additionally, we define the abbreviation [ beta t = t .: Var ].

    The definition below is an almost verbatim copy of the inference rules. The
    one difference is in the beta rule. Instead of using [s.[beta t]]
    directly, we add an equation to the premise.

    This makes the constructor applicable even if the substitution on [s] is
    not of to the special form [beta t]. The resulting equation can then be
    solved using [autosubst]. *)

Inductive step : term -> term -> Prop :=
| step_beta (s1 s2 t : term) :
    s1.[t/] = s2 -> step (App (Lam s1) t) s2
| step_appL (s1 s2 t : term) :
    step s1 s2 -> step (App s1 t) (App s2 t)
| step_appR (s t1 t2 : term) :
    step t1 t2 -> step (App s t1) (App s t2)
| step_lam  (s1 s2 : term) :
    step s1 s2 -> step (Lam s1) (Lam s2).

(** The proof of substitutivity proceeds by induction on the reduction relation.
    In every case we use [autosubst] to simplify the substitution operation and
    apply a constructor. Apart from [step_beta] every case is trivial and solved
    by the tactic of the same name.

    In the case of beta reduction we have to show the equation
    #<div class="block">#
    [s1.[t .: Var].[sigma] = s1.[up sigma].[t.[sigma] .: Var]].
    #</div>#

    This goal can be solved using [autosubst], since both sides of the equation
    are equivalent to the normal form [s1.[t.[sigma] .: sigma]]. *)    

Lemma substitutivity s1 s2 :
  step s1 s2 -> forall sigma, step s1.[sigma] s2.[sigma].
Proof.
  induction 1; constructor; subst; autosubst.
Restart.
  induction 1; intros; simpl; eauto using step; subst.
  constructor. asimpl. reflexivity.
Qed.



(** We define syntax for simple types. *)
Inductive type :=
| Base
| Arr (A B : type).

(** For simplicity, the typing relation uses infinite contexts, that is, substitutions 
    Thus we can reuse the primitives and tactics for substitutions.
*)
Inductive ty (Gamma : var -> type) : term -> type -> Prop :=
| Ty_Var x A :     Gamma x = A -> 
                   ty Gamma (Var x) A
| Ty_Lam s A B :   ty (A .: Gamma) s B -> 
                   ty Gamma (Lam s) (Arr A B)
| Ty_App s t A B : ty Gamma s (Arr A B) -> ty Gamma t A -> 
                   ty Gamma (App s t) B.

(** This lemma is a generalization of the usual weakening lemma and a specialization
    of [ty_subst], which we will prove next.
*)
Lemma ty_ren Gamma s A: 
  ty Gamma s A -> forall Delta xi, 
  Gamma = xi >>> Delta -> 
  ty Delta s.[ren xi] A.
Proof.
  induction 1; intros; subst; asimpl; econstructor; eauto. 
  - eapply IHty. autosubst.
Qed.

(** By generalizing [ty_ren] to substitutions, we obtain that we preserve typing 
    if we replace variables by terms of the same type.
*)
Lemma ty_subst Gamma s A: 
  ty Gamma s A -> forall sigma Delta,
  (forall x, ty Delta (sigma x) (Gamma x)) ->
  ty Delta s.[sigma] A.
Proof.
  induction 1; intros; subst; asimpl; eauto using ty. 
  - econstructor. eapply IHty.
    intros [|] *; asimpl; eauto using ty, ty_ren.
Qed.

(** To show type preservation of the simply typed lambda calculus, we use [ty_subst] to
    justify the typing of the result of the beta reduction.
*)
Lemma ty_pres Gamma s A : 
  ty Gamma s A -> forall s', 
  step s s' -> 
  ty Gamma s' A.
Proof.
  induction 1; intros s' H_step; asimpl;
  inversion H_step; ainv; eauto using ty.
  - eapply ty_subst; try eassumption.
    intros [|]; simpl; eauto using ty.
Qed.