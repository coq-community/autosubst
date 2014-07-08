(** Type classes and notations for substitutions. *)
Require Import Autosubst_Basics Autosubst_MMap.

(**
  [_bind] is used to annotate the position of binders in inductive
  definitions of syntactic objects
*)
Definition _bind (T1 : Type) (T2 : Type) (n : nat) := T2.
Arguments _bind / T1 T2 n.

Notation "{ 'bind' n 'of' T1 'in' T2 }" :=
  (_bind T1 T2 n) (at level 0,
   format "{ 'bind'  n  'of'  T1  'in'  T2 }") : bind_scope.

Notation "{ 'bind' n 'of' T }" :=
  (_bind T T n) (at level 0,
   format "{ 'bind'  n  'of'  T }") : bind_scope.

Notation "{ 'bind' T1 'in' T2 }" :=
  (_bind T1 T2 1) (at level 0,
   format "{ 'bind'  T1  'in'  T2 }") : bind_scope.

Notation "{ 'bind' T }" :=
  (_bind T T 1) (at level 0,
   format "{ 'bind'  T }") : bind_scope.

Open Scope bind_scope.

(**
  Classes for the substitution operations.

  We use singleton classes to obtain the right reduction behaviour with simpl.
  This relies on the feature of simpl which folds fix-bodies.
*)

Class Ids (term : Type) := ids : var -> term.
Class Rename (term : Type) := rename : (var -> var) -> term -> term.
Class Subst (term : Type) := subst : (var -> term) -> term -> term.
Class HSubst (inner outer : Type) := hsubst : (var -> inner) -> outer -> outer.

Arguments ids {_ _} x : simpl never.
Arguments rename {_ _} xi !s /.
Arguments subst {_ _} sigma !s /.
Arguments hsubst {_ _ _} sigma !s / .

Definition scomp {A} `{Subst A} (f : var -> A) (g : var -> A) : var -> A
  := f >>> subst g.
Arguments scomp {A _} f g x /.

Notation "sigma >> tau" := (scomp sigma tau)
  (at level 55, right associativity) : subst_scope.

Notation "s .[ sigma ]" := (subst sigma s)
  (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ]" ) : subst_scope.
Notation "s .[ t /]" := (subst (t .: ids) s)
  (at level 2, t at level 200, left associativity,
   format "s .[ t /]") : subst_scope.
Notation "s .[ t1 , t2 , .. , tn /]" :=
  (subst (scons t1 (scons t2 .. (scons tn ids) .. )) s)
  (at level 2, left associativity,
   format "s '[ ' .[ t1 , '/' t2 , '/' .. , '/' tn /] ']'") : subst_scope.

Notation "s ..[ sigma ]" := (mmap (subst sigma) s)
  (at level 2, sigma at level 200, left associativity,
   format "s ..[ sigma ]" ) : subst_scope.
Notation "s ..[ t /]" := (mmap (subst (t .: ids)) s)
  (at level 2, t at level 200, left associativity,
   format "s ..[ t /]") : subst_scope.
Notation "s ..[ t1 , t2 , .. , tn /]" :=
  (mmap (subst (scons t1 (scons t2 .. (scons tn ids) .. ))) s)
  (at level 2, left associativity,
   format "s '[ ' ..[ t1 , '/' t2 , '/' .. , '/' tn /] ']'") : subst_scope.

Definition hcomp {A B} `{HSubst A B} (f : var -> B) (g : var -> A) : var -> B
  := f >>> hsubst g.
Arguments hcomp {A B _} f g x /.

Notation "sigma >>| tau" := (hcomp sigma tau)
  (at level 55, right associativity) : subst_scope.

Notation "s .|[ sigma ]" := (hsubst sigma s)
  (at level 2, sigma at level 200, left associativity,
   format "s .|[ sigma ]" ) : subst_scope.
Notation "s .|[ t /]" := (hsubst (t .: ids) s)
  (at level 2, t at level 200, left associativity,
   format "s .|[ t /]") : subst_scope.
Notation "s .|[ t1 , t2 , .. , tn /]" :=
  (hsubst (scons t1 (scons t2 .. (scons tn ids) .. )) s)
  (at level 2, left associativity,
   format "s '[ ' .|[ t1 , '/' t2 , '/' .. , '/' tn /] ']'") : subst_scope.

Notation "s ..|[ sigma ]" := (mmap (hsubst sigma) s)
  (at level 2, sigma at level 200, left associativity,
   format "s ..|[ sigma ]" ) : subst_scope.
Notation "s ..|[ t /]" := (mmap (hsubst (t .: ids)) s)
  (at level 2, t at level 200, left associativity,
   format "s ..|[ t /]") : subst_scope.
Notation "s ..|[ t1 , t2 , .. , tn /]" :=
  (mmap (hsubst (scons t1 (scons t2 .. (scons tn ids) .. ))) s)
  (at level 2, left associativity,
   format "s '[ ' ..|[ t1 , '/' t2 , '/' .. , '/' tn /] ']'") : subst_scope.

(** Coercion from renamings to substitutions. *)

Definition ren {T} `{Ids T} (xi : var -> var) : var -> T := xi >>> ids.
Arguments ren {T _} xi x /.

(** Modify a substitution when going below a binder. *)

Definition up {T} `{Ids T} `{Rename T} (sigma : var -> T) : var -> T :=
  ids 0 .: sigma >>> rename (+1).
Arguments up {T _ _} sigma x : simpl never.

Notation upn := (iterate up).

Definition upren (xi : var -> var) : (var -> var) := 0 .: xi >>> S.

(** the essential substitution lemmas *)

Class SubstLemmas (term : Type) {Ids_term : Ids term}
  {Rename_term : Rename term} {Subst_term : Subst term} :=
{
  rename_subst (xi : var -> var) (s : term) :
    rename xi s = s.[ren xi];
  subst_id (s : term) :
    s.[ids] = s;
  id_subst (sigma : var -> term) (x : var) :
    (ids x).[sigma] = sigma x;
  subst_comp (sigma tau : var -> term) (s : term) :
    s.[sigma].[tau] = s.[sigma >> tau]
}.

Class HSubstLemmas (inner outer : Type)
  {Ids_inner : Ids inner} {Subst_inner : Subst inner}
  {Ids_outer : Ids outer}
  {HSubst_inner_outer : HSubst inner outer} :=
{
  hsubst_id (s : outer) :
    s.|[ids : var -> inner] = s;
  id_hsubst (theta : var -> inner) (x : var) :
    (ids x).|[theta] = (ids x);
  hsubst_comp (theta eta : var -> inner) (s : outer) :
    s.|[theta].|[eta] = s.|[theta >> eta]
}.

Class SubstHSubstComp (inner outer : Type)
  {Subst_outer : Subst outer}
  {HSubst_inner_outer : HSubst inner outer} :=

  subst_hsubst_comp (sigma : var -> outer) (tau : var -> inner) (s : outer) :
    s.[sigma].|[tau] = s.|[tau].[sigma >>| tau].

Class HSubstHSubstComp (inner1 inner2 outer : Type)
  {HSubst_inner1_outer : HSubst inner1 outer}
  {HSubst_inner2_outer : HSubst inner2 outer}
  {HSubst_inner2_inner1 : HSubst inner2 inner1} :=

  hsubst_hsubst_comp (sigma : var -> inner1) (tau : var -> inner2) (s : outer) :
    s.|[sigma].|[tau] = s.|[tau].|[sigma >>| tau].

Class HSubstHSubstInd (inner1 inner2 outer : Type)
  {HSubst_inner1_outer : HSubst inner1 outer}
  {HSubst_inner2_outer : HSubst inner2 outer} :=

  hsubst_hsubst_ind (sigma : var -> inner1) (tau : var -> inner2) (s : outer) :
    s.|[sigma].|[tau] = s.|[tau].|[sigma].

(* Local Variables: *)
(* coq-load-path: (("." "Autosubst")) *)
(* End: *)
