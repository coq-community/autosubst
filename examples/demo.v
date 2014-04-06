Require Import Autosubst Contexts.

(** 
The inductive definition of term contains annotations for the automatic generation of the substitution.

"var" is convertible to nat and indicates the constructor used for variables.
There should be exactly one such constructor and it should only have a single argument, which must be of type var.

"bind T" is convertible to T and indicates that a variable is bound in the respective subterm.
*)

Inductive term :=
| TVar (x : var)
| Lam (s : {bind term})
| App (s t : term)
.

(* Now we can fully automatically derive the substitution operations and the corresponding lemmas. This is done by generating instances for the typeclasses Subst and SubstLemmas.

(Subst term) contains the following operations:
  - subst : (var -> term) -> term -> term
    the generic substitution operation
  - Var : var -> term
    a generic term constructor for variables. It is always identical to the single constructor having an argument of type "var". So in this example, "Var" is convertible to "TVar".
  - rename : (var -> var) -> term -> term
    a renaming operations. It is only needed for technical reasons and subsumed by subst. It is mostly hidden in the interface and you should not stumble upon it.

We define the notations:
  - "s.[sigma]" for (subst sigma s)
  - "sigma >> tau" for the composition of sigma and tau, that is, (fun x => (sigma x).[tau])

SubstLemmas contains the following lemmas:
  - subst_comp : forall (s : term) (sigma tau : var -> term), s.[sigma].[tau] = s.[sigma >> tau]
  - subst_id : forall s : term, s.[Var] = s
  - id_subst : forall (x : var) (sigma : var -> term), (Var x).[sigma] = sigma x
  - rename_subst : forall (xi : var -> var) (s : term), rename xi s = s.[ren xi]
where
  ren xi x = Var (xi x)
*)

Instance VarConstr_term : VarConstr term. derive_VarConstr. Defined.
Instance Rename_term : Rename term. derive_Rename. Defined.
Instance Subst_term : Subst term. derive_Subst. Defined.
Instance substLemmas_term : SubstLemmas term. derive_SubstLemmas. Qed.


Inductive step : term -> term -> Prop :=
| Step_Beta s s' t : s' = s.[t .: Var] -> step (App (Lam s) t) s'
| Step_App1 s s' t: step s s' -> step (App s t) (App s' t)
| Step_App2 s t t': step t t' -> step (App s t) (App s t')
| Step_Lam s s' : step s s' -> step (Lam s) (Lam s')
.

Inductive type :=
| Base
| Arr (A B : type)
.

Inductive ty (Gamma : list type) : term -> type -> Prop :=
| Ty_Var x A : atn Gamma x A -> ty Gamma (Var x) A
| Ty_Lam s A B: ty (A :: Gamma) s B -> ty Gamma (Lam s) (Arr A B)
| Ty_App s t A B: ty Gamma s (Arr A B) -> ty Gamma t A -> ty Gamma (App s t) B
.

(** The library defines the tactic autosubst, which simplifies expressions containing substitutions and tries to compute a normal form for substitutions. 
*)

(** This subsumes the usual weakening and reordering lemmas. Context extension and reordering is expressed with the renaming xi, which maps indices referring to the original context to indices referring to the extended context. 
*)

Lemma ty_weak Gamma1 s A:
  ty Gamma1 s A -> forall xi Gamma2,
  (forall x B, atn Gamma1 x B -> atn Gamma2 (xi x) B) ->
  ty Gamma2 s.[ren xi] A.
Proof.
  induction 1; intros; autosubst; eauto using ty.
  constructor. apply IHty. intros [|]; simpl; eauto.
Qed.


(** This is the usual substitutivity lemma for the typing relation extended to parallel substitutions.
*)
Lemma ty_subst Gamma1 s A : 
  ty Gamma1 s A -> forall sigma Gamma2,
  (forall x B, atn Gamma1 x B -> ty Gamma2 (sigma x) B) ->
  ty Gamma2 s.[sigma] A.
Proof.
  induction 1; intros; autosubst; eauto using ty.
  constructor. apply IHty. intros [|]; simpl; eauto using ty, ty_weak.
Qed.

Lemma preservation s t: step s t -> forall A Gamma, ty Gamma s A -> ty Gamma t A.
Proof.
  induction 1; intros; ainv; eauto using ty.
  eapply ty_subst; eauto.
  intros [|]; simpl; intros; subst; eauto using ty.
Qed.

Lemma step_subst s s' : step s s' -> forall sigma, step s.[sigma] s'.[sigma].
Proof.
  induction 1; autosubst; constructor; subst; trivial. now autosubst.
Qed.