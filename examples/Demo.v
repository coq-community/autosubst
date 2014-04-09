(** * Tutorial

    In this tutorial we will use Autosubst to formalize substitutivity and
    subject reduction in the simply typed lambda calculus. *)

Require Import Autosubst List.

(** ** Syntax and the substitution operation

    Types and terms of the simply typed lambda calculus are described by the
    following grammar.

<<
  A, B ::= * | A -> B
  s, t ::= x | s t | \ A. s
>>

    Types are either the base type, or a function type. Terms are variables,
    applications, or abstractions. In order to generate the substitution
    operation for terms we will add some annotations to terms. In this case we
    will have to mark the variable and abstraction constructor with the
    following constructs:

    - [var] is convertible to [nat] and indicates the constructor used for
      variables.
    - [{bind T}] is convertible to [T] and indicates that a variable is bound in
      the respective subterm. *)

Inductive type :=
| TBase
| TFun  (A B : type).

Inductive term :=
| TVar (x : var)
| App  (s t : term)
| Lam  (A : type) (s : {bind term}).

(** Now we can automatically derive the substitution operations and lemmas.
    This is done by generating instances for the following typeclasses:
    - [VarConstr term] provides the generic variable constructor Var for term.
      It is always equivalent to the single constructor having an argument of
      type [var]. In this example, [Var] is convertible to [TVar].
    - [Rename term] provides the renaming operation on term.
    - [Subst term] provides the substitution operation on term and needs a
      [Rename] instance in the presence of binders.
    - [SubstLemmas term] contains proofs for the basic lemmas.

    Each instance is inferred automatically by using the [derive] tactic. *)

Instance VarConstr_term : VarConstr term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

(** At this point we can use the notations:
    - [s.[sigma]] for the application of the substitution sigma to a term s.
    - [sigma >> tau] for the composition of sigma and tau, i.e., the
      substitution [fun x => (sigma x).[tau]].

    SubstLemmas contains the following lemmas:
    - id_subst s x : [(Var x).[sigma] = sigma x]
    - subst_id s : [s.[Var] = s]
    - subst_comp sigma tau : [s.[sigma].[tau] = s.[sigma >> tau]]
    - rename_subst xi s : [rename xi s = s.[ren xi]]
    where [ren xi x = Var (xi x)].

    In addition these lemmas allow you to use the autosubst tactic. *)

(** ** Reduction and substitutivity

    Reductions are defined by the following inference rules:

<<
    s1 \rhd s2        t1 \rhd t2          s1 \rhd s2
  --------------    --------------    ------------------
  s1 t \rhd s2 t    s t1 \rhd s t2    \A. s1 \rhd \A. s2


  ---------------------------
  (\A. s) t \rhd s.[beta t]
>>

    Where [beta t] is notation for the substitution [t .: Var].

    The definition below is an almost verbatim copy of the inference rules. The
    one difference is in the beta rule. Instead of using [s.[beta t]]
    directly, we add an equation to the premise.

<<
   s2 = s1.[beta t]
  ------------------
  (\A. s1) t \rhd s2
>>

    This makes the constructor applicable even if the substitution on [s] is not
    of to the special form [t .: Var]. *)

Inductive step : term -> term -> Prop :=
| Step_Beta (A : type) (s1 s2 t : term) :
    s2 = s1.[beta t] -> step (App (Lam A s1) t) s2
| Step_App1 (s1 s2 t : term) :
    step s1 s2 -> step (App s1 t) (App s2 t)
| Step_App2 (s t1 t2 : term) :
    step t1 t2 -> step (App s t1) (App s t2)
| Step_Lam (A : type) (s1 s2 : term) :
    step s1 s2 -> step (Lam A s1) (Lam A s2).

Lemma step_subst s1 s2 :
  step s1 s2 -> forall sigma, step s1.[sigma] s2.[sigma].
Proof.
(* The proof of substitutivity proceeds by induction on the step relation.
    Every case, except for [Step_Beta] is trivial and solved by eauto. *)
  induction 1; eauto using step.
(* In the beta case we can apply the constructor and simplify the goal. *)
  intros sigma. autosubst. constructor. subst.
(* At this point our goal is to show the equation:
<<
   s1.[beta t].[sigma] = s1.[up sigma].[beta t.[sigma]]
>>
    This is a parallel variant of Barendregt's famous substitution lemma.
    As it is simply an equations between terms with substitutions we can solve
    this goal using autosubst. In this particular case, the equation holds
    because both sides are equivalent to the normal form
    [s1.[t.[sigma] .: sigma]]. *)
  now autosubst.
Qed.

(** ** Type preservation

    The typing relation is defined by the following inference rules.

<<
   Gamma x = A      Gamma |- s : A -> B    Gamma |- t : A
  --------------   ---------------------------------------
  Gamma |- x : A             Gamma |- s t : B

      Gamma, A |- s : B
  -------------------------
   Gamma |- \A. s : A -> B
>>

    We implement contexts as lists and write [A :: Gamma] instead of "Gamma, A".
    Apart from this, we also need to implement the "Gamma x = A" line in the
    variable rule. Since this is just a list lookup we use the [nth_error]
    function from the list library. *)

Inductive ty (Gamma : list type) : term -> type -> Prop :=
| Ty_Var (x : var) (A : type) :
    nth_error Gamma x = value A -> ty Gamma (Var x) A
| Ty_App (A B : type) (s t : term) :
    ty Gamma s (TFun A B) -> ty Gamma t A -> ty Gamma (App s t) B
| Ty_Lam (A B : type) (s : term) :
    ty (A :: Gamma) s B -> ty Gamma (Lam A s) (TFun A B).

(** Our goal for the rest of the tutorial is to show type preservation, that is:
<<
  Gamma |- s : A -> s \rhd t -> Gamma |- t : A
>>
    As usual, this requires a substitution lemma, which in turn requires
    weakening. Using parallel substitutions we can show a general lemma for
    arbitrary substitutions. The weakening lemma is the special case of a
    renaming substitution. *)

Lemma ty_weak Gamma s A :
  ty Gamma s A -> forall Delta xi,
  (forall x B,
     nth_error Gamma x = value B -> nth_error Delta (xi x) = value B) ->
  ty Delta s.[ren xi] A.
Proof.
  induction 1; intros; autosubst; eauto using ty.
  constructor. apply IHty. intros [|]; simpl; eauto.
Qed.

Lemma ty_subst Gamma s A :
  ty Gamma s A -> forall Delta sigma,
  (forall x B, nth_error Gamma x = value B -> ty Delta (sigma x) B) ->
  ty Delta s.[sigma] A.
Proof.
  induction 1; intros; autosubst; eauto using ty.
  constructor. apply IHty. intros [|]; simpl; eauto using ty, ty_weak.
Qed.

Lemma substitution Gamma s t A B :
  ty (A :: Gamma) s B ->
  ty Gamma t A ->
  ty Gamma s.[beta t] B.
Proof.
  intros T1 T2. apply (ty_subst _ _ _ T1). intros [|x] C; simpl; eauto using ty.
  intros H. inversion H; subst; auto.
Qed.

Lemma preservation s t :
  step s t -> forall Gamma A, ty Gamma s A -> ty Gamma t A.
Proof.
  induction 1 as [A' s1 s2 t e|s1 s2 t _ ih|s t1 t2 _ ih|A s1 s2 _ ih];
    intros Gamma B T; inversion_clear T; eauto using ty; subst.
  inversion_clear H. revert H1 H0. apply substitution.
Qed.