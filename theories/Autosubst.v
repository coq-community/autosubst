Require Import Omega List.

Require Export Lib.
Require Import MMap.

(** [_bind] is used to annotate the position of binders in inductive definitions of syntactic objects *)

Definition _bind (T1 : Type) (T2 : Type) (n : T2 -> nat) := T2.

(*
Notation "{ 'in' T2 'as' x 'bind' n 'of' T1 }" :=
  (_bind T1 T2 (fun x => n)) (at level 0, x ident, format
   "{ 'in' T2 'as' x 'bind' n 'of' T1 }") : bind_scope.
*)

Notation "{ 'bind' n 'of' T1 'in' T2 }" :=
  (_bind T1 T2 (fun _ => n)) (at level 0,
   format "{ 'bind'  n  'of'  T1  'in'  T2 }") : bind_scope.

Notation "{ 'bind' n 'of' T }" :=
  (_bind T T (fun _ => n)) (at level 0,
   format "{ 'bind'  n  'of'  T }") : bind_scope.

Notation "{ 'bind' T1 'in' T2 }" :=
  (_bind T1 T2 (fun _ => 1)) (at level 0,
   format "{ 'bind'  T1  'in'  T2 }") : bind_scope.

Notation "{ 'bind' T }" :=
  (_bind T T (fun _ => 1)) (at level 0,
   format "{ 'bind'  T }") : bind_scope.

Open Scope bind_scope.

(** A type synonym for natural numbers used as de Bruijn indices *)
Definition var := nat.

(** The up operation performed when going below a binder, specialized to renamings *)
Definition upren (xi : var -> var) : (var -> var) := 0 .: (fun x => (+1) (xi x)).

(** Classes for the basic substitution operations. 
 They are singleton classes to enable the feature of simpl that folds back fix-bodies.
 *)
Class VarConstr (term : Type) := Var : nat -> term.
Class Rename (term : Type) := rename : (var -> var) -> term -> term.
Class Subst (term : Type) := subst : (var -> term) -> term -> term.
Class SubstOps (term : Type) := {
  SubstOps_VarConstr :> VarConstr term;
  SubstOps_Rename :> Rename term;
  SubstOps_Subst :> Subst term
}.

Arguments Var {_ _} x : simpl never.
Arguments rename {_ _} xi !s /.
Arguments subst {_ _} sigma !s /.

(** The heterogeneous substitution application can substitute a type different from the one it operates on *)
Class HSubst (inner outer : Type) := hsubst : (var -> inner) -> outer -> outer.
Arguments hsubst {_ _ _} sigma !s / .

Notation "sigma >> tau" := (sigma >>> subst tau) (at level 55, right associativity) : subst_scope.
Notation "s .[ sigma ]" := (subst sigma s) (at level 2, sigma at level 200, left associativity, format "s .[ sigma ]" ) : subst_scope.

Notation "sigma >>| tau" := (sigma >>> hsubst tau) (at level 55, right associativity) : subst_scope.
Notation "s .|[ sigma ]" := (hsubst sigma s) (at level 2, sigma at level 200, left associativity, format "s .|[ sigma ]" ) : subst_scope.
Notation "s ..[ sigma ]" := (mmap (subst sigma) s) (at level 2, sigma at level 200, left associativity, format "s ..[ sigma ]" ) : subst_scope.


Notation beta s := (s .: Var) (only parsing).

(** coercion from renamings to substitutions *)

Definition ren {term : Type}{Var_term : VarConstr term} xi (x : var) := Var (xi x).
Arguments ren {_ _} xi x/.

(** the up operation: performed when going below a binder *)

Notation up sigma := ((Var 0) .: sigma >> ren(+1)).
Notation upn := (iter (fun sigma => up sigma)).

(** internal variant for renamings *)

Notation upr sigma := ((Var 0) .: sigma >>> rename (+1)).
Notation uprn := (iter (fun sigma => upr sigma)).

(** the essential substitution lemmas *)

Class Rename_Subst (term : Type) (VarConstr_term : VarConstr term) (Rename_term : Rename term) 
      (Subst_term : Subst term) :=
  rename_subst xi s : rename xi s = s.[ren xi].

Class Subst_Id (term : Type) (VarConstr_term : VarConstr term) (Subst_term : Subst term) := 
  subst_id s : s.[Var] = s.

Class Id_Subst (term : Type) (VarConstr_term : VarConstr term) (Subst_term : Subst term) :=
  id_subst x sigma : (Var x).[sigma] = sigma x.

Class Subst_Comp (term : Type) (Subst_term : Subst term) :=
  subst_comp s sigma tau : s.[sigma].[tau] = s.[sigma >> tau].

Class SubstLemmas (term : Type) {VarConstr_term : VarConstr term} {Rename_term : Rename term} 
      {Subst_term : Subst term} := {
  SubstLemmas_Rename_Subst :> Rename_Subst term _ _ _;
  SubstLemmas_Subst_Id :> Subst_Id term _ _;
  SubstLemmas_Id_Subst :> Id_Subst term _ _;
  SubstLemmas_Subst_Comp :> Subst_Comp term _
}.

Class HSubst_Comp 
      (inner outer : Type)
      (Subst_inner : Subst inner)
      (HSubst_inner_outer : HSubst inner outer) := hsubst_comp s sigma tau : s.|[sigma].|[tau] = s.|[sigma >> tau].

Class HSubst_Id (inner outer : Type) 
      (VarConstr_inner : VarConstr inner) (HSubst_inner_outer : HSubst inner outer) :=
  hsubst_id s : s.|[Var] = s.

Class Id_HSubst (inner outer : Type) 
      (VarConstr_outer : VarConstr outer) (HSubst_inner_outer : HSubst inner outer) :=
  id_hsubst sigma x : (Var x).|[sigma] = Var x.

Class HSubstLemmas 
      (inner outer : Type)
      (VarConstr_inner : VarConstr inner)
      (Subst_inner : Subst inner)
      (VarConstr_outer : VarConstr outer)
      (HSubst_inner_outer : HSubst inner outer) := {
  HSubstLemmas_HSubst_Id :> HSubst_Id inner outer _ _ ;
  HSubstLemmas_Id_HSubst :> Id_HSubst inner outer _ _ ;
  HSubstLemmas_Hsubst_comp :> HSubst_Comp inner outer _ _
}.

Class SubstHSubstComp 
      (inner outer : Type)
      (Subst_outer : Subst outer)
      (HSubst_inner_outer : HSubst inner outer) := 
  subst_hsubst_comp s sigma tau : s.[sigma].|[tau] = s.|[tau].[sigma >>| tau]
.

Class HSubstHSubstComp
      (inner1 inner2 outer : Type)
      (HSubst_inner1_outer : HSubst inner1 outer)
      (HSubst_inner2_outer : HSubst inner2 outer)
      (HSubst_inner2_inner1 : HSubst inner2 inner1) :=
hsubst_hsubst_comp s sigma tau : s.|[sigma].|[tau] = s.|[tau].|[sigma >>| tau].

Class HSubstHSubstInd
      (inner1 inner2 outer : Type)
      (HSubst_inner1_outer : HSubst inner1 outer)
      (HSubst_inner2_outer : HSubst inner2 outer) :=
hsubst_hsubst_ind s (sigma : var -> inner1) (tau : var -> inner2) : s.|[sigma].|[tau] = s.|[tau].|[sigma].


(** the derived substitution lemmas *)

Section LemmasForSubst.

Context {term : Type}.
Context {VarConstr_term : VarConstr term} {Rename_term : Rename term} {Subst_term : Subst term}.
Context {RenameSubst_term : Rename_Subst term _ _ _}
        {Subst_Id_term : Subst_Id term _ _}
        {Id_Subst_term : Id_Subst term _ _}
        {Subst_Comp_term : Subst_Comp term _}
.

Ltac autosubst := 
  repeat (try rewrite funcomp_scons_distr;
  try rewrite rename_subst;
  simpl;
  try rewrite subst_id;
  try rewrite id_subst;
  try rewrite subst_comp).

Lemma rename_subst' xi : rename xi = subst (ren xi).
Proof. f_ext. apply rename_subst. Qed.

Lemma Var_comp_l (sigma : var -> term) : Var >> sigma = sigma.
Proof. f_ext. intros. unfold funcomp. now autosubst. Qed.

Lemma scons_lift (x y: var) : y = S x -> Var x .: ren (+ y) = ren (+x).
Proof.
  unfold var in *. intros. subst.
  f_ext; intro y; destruct y; unfold lift; simpl; f_equal; omega.
Qed.

Lemma scons_subst_lift sigma s n : n > 0 -> sigma (pred n) = s -> s .: (ren(+n) >> sigma) = ren(+ pred n) >> sigma. 
Proof.
  intros. subst.
  f_ext. intros [|] *; autosubst; f_equal; unfold lift; unfold var in *; omega.
Qed.

Lemma lift_scons {X} (s : X) sigma n: n > 0 -> (+ n) >>> (s .: sigma) = (+ pred n) >>> sigma.
Proof.
  intros. destruct n. omega. f_ext. intros [|] *; repeat autosubst; repeat first[omega | f_equal].
Qed.

Lemma lift0_id n: n = 0 -> (+n) = id.
Proof. intros. subst. reflexivity. Qed.

Lemma ren_id : ren id = Var. 
Proof. reflexivity. Qed.

Lemma ren_comp xi zeta : ren (xi >>> zeta) = xi >>> ren zeta.
Proof.
  f_ext. intro. now autosubst.
Qed.

Lemma ren_left xi sigma : ren xi >> sigma = xi >>> sigma.
Proof. f_ext. intros. autosubst. reflexivity. Qed.

Lemma ren_scons x xi : ren (x .: xi) = Var x .: ren xi.
Proof.
  f_ext. now intros [|].
Qed.

Lemma lift_comp n m: (+n) >>> ren(+m) = ren(+(n+m)).
Proof.
  unfold ren. unfold lift. f_ext. intro. autosubst. f_equal. unfold var in *. omega.
Qed.

Lemma subst_id' : subst Var = id.
Proof. f_ext. exact subst_id. Qed.


Lemma subst_comp' sigma tau : subst tau >> sigma = subst (tau >> sigma).
Proof.
  f_ext. intro. now autosubst.
Qed.

Lemma upn_upn_comp n sigma tau : upn n (sigma >> tau) = upn n sigma >> upn n tau.
Proof.
  induction n; autosubst. 
  - reflexivity. 
  - repeat rewrite iter_S. rewrite IHn. autosubst. 
    f_equal. repeat rewrite funcomp_assoc. repeat rewrite subst_comp'.
    rewrite ren_left.
    rewrite lift_scons by omega.
    simpl.
    rewrite (lift0_id 0) by omega.
    now rewrite id_funcomp.
Qed.

Lemma upn_var n : upn n Var = Var.
Proof.
  induction n; autosubst.
  - reflexivity.
  - rewrite iter_S. autorew. f_ext. intros [|] *. reflexivity.
    now autosubst.
Qed.

End LemmasForSubst.


(** derived substitution lemmas for heterogeneous substitutions *)

Section LemmasForHSubst.

Context {inner outer : Type}.

Context {VarConstr_inner : VarConstr inner} {Rename_inner : Rename inner} {Subst_inner : Subst inner}.
Context {SubstLemmas_inner : SubstLemmas inner}.

Context {VarConstr_outer : VarConstr outer} {Rename_outer : Rename outer} {Subst_outer : Subst outer}.
Context {SubstLemmas_outer : SubstLemmas outer}.

Context {HSubst_inner_outer : HSubst inner outer}.
Context {HSubstLemmas_inner_outer : HSubstLemmas inner outer _ _ _ _}.
Context {SubstHSubstComp_inner_outer : SubstHSubstComp inner outer _ _}.


Ltac autosubst := 
  simpl;
  try rewrite hsubst_id;
  try rewrite id_hsubst;
  try rewrite hsubst_comp;
  try rewrite subst_hsubst_comp.

Lemma ren_hcomp (sigma : var -> inner) xi : ren xi >>| sigma = ren xi.
Proof.
  f_ext. intros. now autosubst.
Qed.

Lemma Var_hcomp_l (sigma : var -> inner) : Var >>| sigma = Var.
Proof.
  apply ren_hcomp.
Qed.


Lemma hsubst_id' : hsubst Var = id.
Proof. f_ext. exact hsubst_id. Qed.


Lemma comp_hcomp (sigma1 sigma2 : var -> outer) (sigma3 : var -> inner) : (sigma1 >> sigma2) >>| sigma3 = (sigma1 >>| sigma3) >> (sigma2 >>| sigma3).
Proof.
  f_ext. intros. now autosubst.
Qed.

Lemma hsubst_comp' sigma tau : hsubst sigma >>| tau = hsubst (sigma >> tau).
Proof.
  f_ext. intro. now autosubst.
Qed.

Lemma subst_hsubst_comp' sigma tau : subst sigma >>| tau = hsubst tau >> (sigma >>| tau).
Proof.
  f_ext. intros. now autosubst.
Qed.  

End LemmasForHSubst.


(** the autosubst automation tactic *)

Hint Rewrite @rename_subst' @subst_comp (**@to_lift*) @Var_comp_l @funcomp_scons_distr using exact _ : autosubst.
Hint Rewrite @scons_lift lift0_id (lift0_id 0) using solve[exact _ | unfold lift in *; unfold var in *; omega] : autosubst.
Hint Rewrite @scons_subst_lift @lift_scons using solve[exact _ | simpl; unfold lift in *; unfold var in *; repeat first [omega | f_equal] ] : autosubst.  
Hint Rewrite @funcomp_assoc @id_funcomp @funcomp_id @subst_comp' @subst_id' @ren_id @ren_left @ren_comp @ren_scons @lift_comp @upn_upn_comp @upn_var @NPeano.Nat.add_1_r @iter_S @iter_0 using exact _ : autosubst.
Hint Rewrite @hsubst_id' @id_hsubst @hsubst_comp @subst_hsubst_comp
             @ren_hcomp @Var_hcomp_l @comp_hcomp @hsubst_comp' @subst_hsubst_comp' using exact _ : autosubst.

Ltac autosubst :=
  trivial;
  repeat match goal with [|- context[Var ?x]] => let s := constr:(Var x) in progress change (Var x) with s end;
  repeat match goal with [|- appcontext[ren ?xi]] => let s := constr:(ren xi) in progress change (ren xi) with s end;
  repeat match goal with [|- appcontext[rename ?xi]] => let s := constr:(rename xi) in progress change (rename xi) with s end;
  repeat match goal with [|- appcontext[subst ?sigma]] => let s := constr:(subst sigma) in progress change (subst sigma) with s end;
  repeat match goal with [|- appcontext[hsubst ?sigma]] => let s := constr:(hsubst sigma) in progress change (hsubst sigma) with s end;
  repeat first[ 
           progress (
               rewrite ?rename_subst';
               simpl;
               try unfold _bind;
               autorewrite with autosubst;
               rewrite ?subst_hsubst_comp, ?ren_hcomp, ?hsubst_id', ?hsubst_comp', ?hsubst_comp
             )
         | match goal with [|- context[(_ .: _) ?x]] => 
             match goal with [y : _ |- _ ] => unify y x; destruct x; simpl end
           end];
  (try (unfold lift in *; unfold var in *; simpl; repeat first [omega | f_equal]; fail));
  repeat (try rewrite <- ren_comp; try rewrite <- ren_scons).

Ltac autosubstH H :=
  let T_H := typeof H in
  repeat match T_H with context[Var ?x] => let s := constr:(Var x) in progress change (Var x) with s in H end;
  repeat match T_H with appcontext[ren ?xi] => let s := constr:(ren xi) in progress change (ren xi) with s in H end;
  repeat match T_H with appcontext[rename ?xi] => let s := constr:(rename xi) in progress change (rename xi) with s in H end;
  repeat match T_H with appcontext[subst ?sigma] => let s := constr:(subst sigma) in progress change (subst sigma) with s in H end;
  repeat match T_H with appcontext[hsubst ?sigma] => let s := constr:(hsubst sigma) in progress change (hsubst sigma) with s in H end;
  repeat first[
           progress (
               rewrite ?rename_subst' in H;
               simpl in H;
               try unfold _bind in H;
               autorewrite with autosubst in H;
               rewrite ?subst_hsubst_comp, ?ren_hcomp, ?hsubst_id', ?hsubst_comp', ?hsubst_comp in H
             )|
            match typeof H with context[(_ .: _) ?x] => 
             match goal with [y : _ |- _ ] => unify y x; destruct x; simpl in H end
           end
         ];
  repeat (try rewrite <- ren_comp in H; try rewrite <- ren_scons in H).

Tactic Notation "autosubst" "in" ident(H) := autosubstH H.

Tactic Notation "autosubst" "in" "*" := autosubst; (in_all autosubstH).


(** tactics to derive typeclass instances *)

Ltac app_var := match goal with [ |- var] => assumption end.

Ltac derive_VarConstr :=
intro; solve[constructor 1; [app_var] | constructor 2; [app_var] | constructor 3; [app_var] | constructor 4; [app_var] | constructor 5; [app_var] | constructor 6; [app_var] | constructor 7; [app_var] | constructor 8; [app_var] | constructor 9; [app_var] | constructor 10; [app_var] | constructor 11; [app_var] | constructor 12; [app_var] | constructor 13; [app_var] | constructor 14; [app_var] | constructor 15; [app_var] | constructor 16; [app_var] | constructor 17; [app_var] | constructor 18; [app_var] | constructor 19; [app_var] | constructor 20].

Ltac derive_Rename :=
  hnf; 
  fix rename 2; intros xi s;
  destruct s eqn:E;
  let term := typeof s in
  match goal with [E : s = ?s' |- _] =>
    let rec map s := (match s with 
      | ?s1 ?s2 => 
        let s1' := map s1 in
        let s2_T := typeof s2 in
        let s2' := match s2_T with 
          | term => constr:(rename xi s2) 
          | var => constr:(xi s2)
          | _bind term _ ?n => constr:(rename (iter upren (n s2) xi) s2)
          | _bind term _ ?n => constr:(mmap(rename (iter upren (n s2) xi)) s2)
          | context[term] => constr:(rename xi s2)
          | context[term] => constr:(mmap(rename xi) s2)
          | _ => s2 
        end in
        constr:(s1' s2')
      | _ => s 
    end) in 
    let t' := map s' in 
    exact t'
  end.

Ltac has_var s := 
  match s with 
    | ?s1 ?s2 => 
      match has_var s1 with 
        | Some ?x => constr:(Some x)
        | _ => 
          match typeof s2 with 
            | var => constr:(Some s2) 
            | _ => None
          end 
      end
    | _ => None
  end.


Notation _up_ := 
  (fun sigma => (Var 0) .: (sigma >>> rename (+1))) (only parsing).

Ltac derive_Subst :=
  match goal with [ |- Subst ?term] =>
  hnf;
  let subst' := fresh "_subst" in
  fix subst' 2;
  pose (subst' : Subst term);
  let sigma := fresh "sigma" in
  let s := fresh "s" in
  intros sigma s;
  destruct s eqn:E;
  let term := typeof s in
  match goal with [E : s = ?s' |- _] =>
    let rec map s := (match s with 
      | ?s1 ?s2 => 
        let s1' := map s1 in
        let s2_T := typeof s2 in
        let s2' := match s2_T with 
          | term => constr:(subst sigma s2) 
          | _bind term _ ?n => constr:(subst (iter _up_ (n s2) sigma) s2)
          | _bind term _ ?n => constr:(mmap (subst (iter _up_ (n s2) sigma)) s2)
          | _bind ?term'  _ ?n => constr:(subst (sigma >>| (ren(+(n s2)) : var -> term') ) s2)
          | _bind ?term'  _ ?n => constr:(mmap(subst (sigma >>| (ren(+(n s2)) : var -> term'))) s2)
          | context[term] => constr:(subst sigma s2)
          | context[term] => constr:(mmap(subst sigma) s2)
          | _ => s2 
        end in constr:(s1' s2')
      | _ => s 
    end) in 
    match has_var s' with 
      | Some ?v => exact (sigma v)
      | _ => let t' := map s' in
             refine t'
    end
  end
  end.

Ltac derive_SubstOps := 
  match goal with [|- SubstOps ?term] =>
  assert (VarConstr_term : VarConstr term) by derive_VarConstr;
  assert (Rename_term : Rename term ) by derive_Rename;
  assert (Subst_term : Subst term) by derive_Subst;
  constructor; assumption
  end.

Ltac derive_SubstLemmas :=
  match goal with [ |- @SubstLemmas ?term ?VarConstr_term ?Rename_term ?Subst_term] =>
  let rename := constr:(@rename term Rename_term) in
  let subst := constr:(@subst term Subst_term) in
  let Var := constr:(@Var term VarConstr_term) in

  assert(up_upr : forall n xi,
         iter (fun sigma : nat -> term => Var 0 .: sigma >>> rename (+1)) n (ren xi) = ren (iter upren n xi)) by (
  let n := fresh "n" in intros n ?;
  induction n; f_ext; simpl; trivial; 
  intros [|]; intros; simpl; repeat rewrite iter_S; trivial; autorew; now simpl
  );

  assert(rename_subst : forall xi : var -> var, rename xi = subst (ren xi)) by (
  let xi := fresh "xi" in intros xi; 
  f_ext; 
  let s := fresh "s" in intros s;
  revert xi s; 
  let IH := fresh "IH_rename_subst" in
  fix IH 2; intros xi s; destruct s;
  intros; simpl; rewrite ?mmap_inv; trivial; autorew; repeat rewrite (mmap_ext (IH _)); now trivial
  );

  assert(iter_up_Var : forall n, iter (fun sigma : nat -> term => up sigma) n Var = Var) by (
    let n := fresh "n" in intros n; induction n;
    f_ext; intros [|]; try rewrite iter_S;
    simpl; autorew; trivial; autorew; now autosubst 
  );

  assert(subst_id : forall s : term, subst Var s = id s) by (
  let IH := fresh "IH_subst_id" in
  fix IH 1;
  let s := fresh "s" in intros s;
  destruct s;
  simpl; f_equal; eauto; 
  rewrite ?rename_subst, ?iter_up_Var, ?(mmap_ext IH); 
  autorew; msimpl 
  );

  assert(id_subst : forall (x : var) (sigma : var -> term), subst sigma (Var x) = sigma x) by (
  intros; reflexivity 
  );

  assert(iter_ren_subst_comp : 
    forall n xi sigma, ren (iter upren n xi) >> iter (fun sigma => up sigma) n sigma = iter (fun sigma => up sigma) n (ren xi >> sigma)) by (
  let n := fresh "n" in intros n; 
  let IHn := fresh "IHn" in induction n as [| n IHn]; intros; trivial; 
  repeat rewrite iter_S; f_ext; intros [|] *; trivial; 
  simpl; trivial; f_equal; now rewrite <- IHn 
  );

  assert(rename_subst_comp : forall sigma xi s, (rename xi s).[sigma] = s.[ren xi >> sigma]) by (
  let IH := fresh "IH_rename_subst_comp" in
  fix IH 3;
  intros ??; let s := fresh "s" in intros s; destruct s;
  intros; simpl; f_equal; trivial; autorew; repeat rewrite <- rename_subst;
  msimpl; try (unfold funcomp at 1; rewrite (mmap_ext (IH _ _)));
  f_equal; f_equal; repeat rewrite mmap_inv; now autorew
  );

  assert(rename_comp : forall xi zeta s, s.[ren xi].[ren zeta] = s.[ren(xi >>> zeta)]) by (
  intros; repeat rewrite <- rename_subst; rewrite rename_subst;
  rewrite rename_subst_comp; now rewrite rename_subst 
  );

  assert (iter_subst_ren_comp : 
    forall n sigma xi , iter (fun sigma => up sigma) n sigma >> ren (iter upren n xi) = iter (fun sigma => up sigma) n (sigma >> ren xi)) by (
  let n := fresh "n" in intros n; 
  let IHn := fresh "IHn" in induction n as [| n IHn]; intros; trivial; 
  repeat rewrite iter_S; f_ext; intros [|] *; trivial; simpl; rewrite <- IHn; 
  simpl; now autorew 
  );

  assert(subst_rename_comp : forall sigma xi s, rename xi s.[sigma] = s.[sigma >> (ren xi)]) by (
  let IH := fresh "IH_subst_rename_comp" in
  fix IH 3; let s := fresh "s" in intros ? ? s; destruct s;
  intros; simpl; rewrite ?mmap_inv; autorew; autosubst; rewrite ?ren_hcomp; trivial; f_equal;
  msimpl; repeat rewrite <- rename_subst; try (unfold funcomp at 1; rewrite (mmap_ext (IH _ _)));
  repeat f_equal; eauto; now autorew
  );

  assert(renS_up : forall sigma s, s.[ren(+1)].[up sigma] = s.[sigma].[ren(+1)]) by (
  intros; rewrite <- rename_subst;
  rewrite subst_rename_comp; rewrite rename_subst_comp;
  f_equal; f_ext; intros; simpl; now rewrite rename_subst
  );

  assert(iter_comp : 
    forall n sigma tau, iter (fun sigma => up sigma) n sigma >> iter (fun sigma => up sigma) n tau = iter (fun sigma => up sigma) n (sigma >> tau)) by (
  let n := fresh "n" in let IHn := fresh "IHn" in
  intros n;
  induction n as [|n IHn]; intros; trivial; repeat rewrite iter_S; 
  f_ext; intros [|]; intros; simpl; trivial;
  rewrite renS_up; f_equal;
  now rewrite <- IHn 
  );

  assert(subst_comp : forall (sigma tau : var -> term) (s : term), s.[sigma].[tau] = s.[sigma >> tau]) by (
  let IH := fresh "IH_subst_comp" in
  fix IH 3;
  let s := fresh "s" in
  intros ? ? s; destruct s; intros; simpl; rewrite ?mmap_inv; 
  f_equal; trivial; try rewrite mmap_comp; autorew; autosubst; trivial;
  try (unfold funcomp at 1; rewrite (mmap_ext (IH _ _))); 
  repeat f_equal; now autorew
  );

  constructor; hnf; intros; autorew; now eauto
  end.


Ltac derive_HSubst :=
  hnf; match goal with [|- (var -> ?inner) -> ?outer -> ?outer] =>
  let hsubst' := fresh "_hsubst" in
  fix hsubst' 2; 
  pose(hsubst' : HSubst inner outer);
  let s := fresh "s" in
  let sigma := fresh "sigma" in
  intros sigma s;
  destruct s eqn:E;
  match goal with 
      [E : s = ?s' |- _] =>
      let rec map s := 
          (match s with 
               ?s1 ?s2 => 
               let s1' := map s1 in
               let s2_T := typeof s2 in
               let s2' := match s2_T with 
                           | inner => constr:(s2.[sigma])
                           | outer => constr:(hsubst sigma s2)
                           | _bind inner outer ?n => constr:(hsubst (iter (fun sigma => up sigma) (n s2) sigma) s2)
                           | _bind _ outer _ => constr:(hsubst sigma s2)
                           | _bind inner inner ?n => constr:(s2.[iter (fun sigma => up sigma) (n s2) sigma])
                           | _bind _ inner _ => constr:(s2.[sigma])
                           | _ => s2 
                         end in
               constr:(s1' s2')
             | _ => s end) in 
      match has_var s' with 
          | Some ?v => exact (sigma v)
          | _ => let t' := map s' in try exact t'
      end
  end
  end.

Ltac derive_HSubstLemmas :=
  match goal with [|- HSubstLemmas ?inner ?outer _ _ _ _ ] =>

  assert(ren_hcomp : forall (xi : var -> var) (sigma : var -> inner), (ren xi : var -> outer) >>| sigma = ren xi) 
  by reflexivity;

  assert(hsubst_comp : forall (s : outer) (sigma tau : var -> inner), s.|[sigma].|[tau] = s.|[sigma >> tau]) 
  by( intros s; induction s; intros; autosubst; autorew; now autosubst );

  constructor; hnf;
  [induction 0; autosubst; now autorew |
  reflexivity |
  exact hsubst_comp] 
  end.

Ltac derive_SubstHSubstComp :=
  assert(rename_hsubst_comp : forall s sigma xi, (rename xi s).|[sigma] = rename xi s.|[sigma]) by (
  let IH := fresh "IH" in let s := fresh "s" in
  fix IH 1; intro s; destruct s; intros; simpl; autorew; trivial);

  assert(rename_hsubst_comp' : forall tau xi, rename xi >>| tau = hsubst tau >>> rename xi) by (
  intros; f_ext; intros; now simpl);

  hnf;
  let IH := fresh "IH" in fix IH 1;
  let s := fresh "s" in intros s; 
  destruct s; intros; simpl; trivial; autorew;
  f_equal; f_equal;
  f_ext; intros; simpl; rewrite ?hsubst_comp; now autosubst.


(** some additional lemmas *)

Section AdditionalLemmas.

Context {term : Type}.
Context {VarConstr_term : VarConstr term} {Rename_term : Rename term} {Subst_term : Subst term}.
Context {subst_lemmas : SubstLemmas term}.

Lemma lift_inj (A B : term) n : A.[ren(+n)] = B.[ren(+n)] -> A = B.
Proof.
  intros H. 
  apply (f_equal (subst (ren (fun x => x - n)))) in H.
  autosubst in H.
  unfold funcomp in H.
  unfold lift in H.
  cutrewrite ((fun x : var => n + x - n) = id) in H.
  now autosubst in H.
  f_ext. intros x. simpl. omega.
Qed.

Lemma ren_uncomp A xi zeta : A.[ren (xi >>> zeta)] = A.[ren xi].[ren zeta].
Proof.
  now autosubst.
Qed.

End AdditionalLemmas.

(** User facing derive tactic *)

Tactic Notation "derive" :=
  match goal with
    | |- VarConstr _ => derive_VarConstr
    | |- Rename _ => derive_Rename
    | |- Subst _ => derive_Subst
    | |- SubstLemmas _ => derive_SubstLemmas
  end.