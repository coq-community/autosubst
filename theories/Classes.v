
(** Type classes and notations for substitutions. *)
Require Import Autosubst.Basics Autosubst.MMap Autosubst.Decidable Autosubst.Sorts.

Notation substitution term := (vec (fun o => var -> term o)).


(**
  [_bind] is used to annotate the position of binders in inductive
  definitions of syntactic objects
 *)
Definition _bind {sort : Set} (o : sort) (T : Type) (n : nat) := T.
Arguments _bind / {sort} o T n.

Notation "{ 'bind' n 'of' o 'in' T }" :=
  (_bind o T n) (at level 0,
   format "{ 'bind'  n  'of'  o  'in'  T }") : bind_scope.

Notation "{ 'bind' o 'in' T }" :=
  (_bind o T 1) (at level 0,
                   format "{ 'bind'  o  'in'  T }") : bind_scope.

Notation "{ 'bind' T }" :=
  (_bind Sort1_1 T 1) (at level 0,
   format "{ 'bind'  T }") : bind_scope.

Open Scope bind_scope.

(**
  Classes for the substitution operations.

  We use singleton classes to obtain the right reduction behaviour with simpl.
  This relies on the feature of simpl which folds fix-bodies.
 *)

Section SubstOps.
  Context {sort : Type}
          {dec_eq_sort : forall a b : sort, Dec (a = b)}.

  Definition upd (o : sort) {T : sort -> Type} (x : T o) (f : forall o, T o) : forall o, T o.
    refine (fun o' => match decide (o = o') with
                       | inl p => _
                       | inr _ => f o' end).
    subst. exact x.
  Defined.
  Global Arguments upd !o {T} x f !o0/.
  Context {Vector_sort : Vector sort}.

  Lemma upd_upd o {T : sort -> Type} (x y n: T o) f : upd o x (upd o y f) = upd o x f.
  Proof.  f_ext. intro o'. unfold upd. decide(o = o'); now subst.  Qed.

  Definition updV (o : sort) {term : sort -> Type} (sigma : var -> term o) (v : substitution term) : substitution term :=
    newV (upd o sigma (getV v)).
  Global Arguments updV o {term} sigma v.

  Definition mapV {term : sort -> Type} (f : forall o, (var -> term o) -> (var -> term o)) (v : substitution term) : substitution term :=
    newV (fun o => f o (getV v o)).
  Global Arguments mapV {term} f v.

  Definition funcompV {term : sort -> Type} (v : substitution term) (f : forall o, term o -> term o) : substitution term := @mapV term (fun o x => x >> (f o)) v.
  Global Arguments funcompV {term} v f.

  Context (term : sort -> Type).

  Class VarConstr := Var : (forall o, var -> term o).
  Class Rename := rename : (sort -> var -> var) -> forall o : sort, term o -> term o.
  Class Subst := subst : (substitution term) -> forall {o : sort}, term o -> term o.

End SubstOps.
Arguments Var {sort term VarConstr} o x.
Arguments rename {sort term Rename} xi [o] !s/.
Arguments subst {sort Vector_sort term Subst} sigma [o] !s/.

Notation ids := (Var _).

Notation "^ sigma" := (subst sigma (o:= _)) (at level 56, right associativity) : subst_scope.
(* JK: is it possible/desirable to format this without a white space? *)

Notation "v |>> f" := (funcompV v f)
  (at level 56, right associativity) : subst_scope.

Notation "s .|[ sigma1 , sigma2 , .. , sigman ]" := (subst (pair .. (pair sigma1 sigma2) .. sigman) s)
  (at level 2, left associativity,
   format "s .|[ sigma1 , sigma2 , .. , sigman ]" ) : subst_scope.

Notation "s .|[ sigma ]" := (subst sigma s)
  (at level 2, sigma at level 200, left associativity,
   format "s .|[ sigma ]" ) : subst_scope.

Notation "s ..|[ sigma ]" := (mmap (subst sigma) s)
  (at level 2, sigma at level 200, left associativity,
   format "s ..|[ sigma ]" ) : subst_scope.




Section Classes.

  Context {sort : Type}
          {dec_eq_sort : forall a b : sort, Dec (a = b)}.
  Context {Vector_sort : Vector sort}.

  Context {term : sort -> Type}.

  Context {VarConstr_term : VarConstr term} {Rename_term : Rename term} {Subst_term : Subst term}.


  Definition idr : sort -> var -> var := fun _ => id.
  Definition idsV := newV Var.

  (** Coercion from renamings to substitutions. *)

  Definition renV (xi : sort -> var -> var) := newV (xi >>2 Var).


  (** Modify a substitution when going below a binder. *)


  Definition up (o : sort) (sigma : substitution term) : substitution term :=
    updV o (Var o 0 .: getV sigma o >> rename (upd o (+1) idr) (o := _)) (sigma |>> rename (upd o (+1) idr)).
  Global Arguments up o sigma : simpl never.

  Notation upn := (iterate up).

  Definition upren (o : sort) (xi : sort -> var -> var) : sort -> var -> var :=
    upd o (0 .: (xi o >> S)) xi.
  Global Arguments upren o xi o' x/.


  (** the essential substitution lemmas *)


 Class SubstLemmas  :=
    {
      rename_subst (xi : sort -> var -> var) (o : sort) (s : term o) :
        rename xi s = subst (renV xi) s;
      subst_id (o : sort) (s : term o) :
        s.|[newV Var] = s;
      id_subst (sigma : substitution term) (o : sort) (x : var) :
        (Var o x).|[sigma] = getV sigma o x;
      subst_comp (sigma tau : substitution term) (o : sort) (s : term o) :
        s.|[sigma].|[tau] = s.|[sigma |>> subst tau]
    }.

 Definition subst1 {o1 o2 : sort} (sigma : var -> term o2) (s : term o1) := s.|[updV o2 sigma idsV].

End Classes.
Arguments up {sort dec_eq_sort Vector_sort term VarConstr_term Rename_term} o sigma : simpl never.
Arguments renV {sort Vector_sort term VarConstr_term} xi : simpl never.
Arguments SubstLemmas {sort Vector_sort} term {VarConstr_term Rename_term Subst_term}.

Arguments idr {sort} o/ x.

Arguments newV : simpl never.
Arguments getV {sort Vector T} v o.
Arguments funcompV {sort Vector_sort term} !v f.

Arguments subst1 : simpl never.

Notation ren o xi := (xi >> Var o).
Notation "s .[ sigma ]" := (subst1 sigma s)
  (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ]" ) : subst_scope.
