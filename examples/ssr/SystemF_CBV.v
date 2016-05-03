(** * Normalization of Call-By-Value System F *)

Require Import Autosubst.Autosubst_Basics Autosubst.Autosubst_Derive Autosubst.Autosubst_MMap.

(* Set Universe Polymorphism. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** **** Definitions *)

Require Import Decidable.

Definition _bind {sort : Set} (o : sort) (T : Type) (n : nat) := T.
Arguments _bind / {sort} o T n.


Notation "{ 'bind' n 'of' T1 'in' T2 }" :=
  (_bind T1 T2 n) (at level 0,
   format "{ 'bind'  n  'of'  T1  'in'  T2 }") : bind_scope.

Notation "{ 'bind' T1 'in' T2 }" :=
  (_bind T1 T2 1) (at level 0,
   format "{ 'bind'  T1  'in'  T2 }") : bind_scope.

Open Scope bind_scope.



(* Goal forall s t,  Arr s t = VarC Ty 3 -> s = t. intros. inversion H. *)

Class Vector (sort : Type) :=
  {
    vec : (sort -> Type) -> Type;
    getV {T : sort -> Type} : vec T -> forall o : sort, T o;
    newV {T : sort -> Type} : (forall o : sort, T o) -> vec T;
    getV_newV {T : sort -> Type} (f : forall o, T o) : getV (newV f) = f 
  }.

Notation substitution term := (vec (fun o => var -> term o)).

Section SubstOps.
  Context {sort : Type}
          {dec_eq_sort : forall a b : sort, Dec (a = b)}.

  Definition upd (o : sort) {T : sort -> Type} (x : T o) (f : forall o, T o) : forall o, T o.
    refine (fun o' => match decide (o = o') with
                       | left p => _
                       | right _ => f o' end).
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
  
  Definition funcompV {term : sort -> Type} (v : substitution term) (f : forall o, term o -> term o) : substitution term := @mapV term (fun o x => x >>> (f o)) v.
  Global Arguments funcompV {term} v f.

  Context {term : sort -> Type}.

  Class VarConstr := ids : (forall o, var -> term o).
  Global Arguments ids {VarConstr} o x.
  Class Rename := rename : (sort -> var -> var) -> forall o : sort, term o -> term o.
  Global Arguments rename {Rename} xi [o] !s/.
  Class Subst := subst : (substitution term) -> forall {o : sort}, term o -> term o.
  Global Arguments subst {Subst} sigma [o] !s/.

End SubstOps.

Arguments VarConstr {sort} term.
Arguments Rename {sort} term.
Arguments Subst {sort} {Vector_sort} term.
(* Notation subst := (_subst (Subst:=$(exact _ )$)). *)


Definition dfuncomp2 {A B C D} (f : forall a : A, B -> C) (g : forall a : A, C -> D a) a := f a >>> g a .
Arguments dfuncomp2 {A B C D} f g a / x.

Notation "f >>2 g" := (dfuncomp2 f g)
  (at level 56, left associativity) : subst_scope.


Notation "v |>> f" := (funcompV v f)
  (at level 56, left associativity) : msubst_scope.


Notation "sigma >> tau" := (sigma >>> subst tau)
  (at level 56, left associativity) : subst_scope.


(* Notation "s .[ ( sigma_1 ; sigma_2 ; .. ; sigma_n ) ]" := *)
(*   (subst ((fun p : (fun T => prod ( .. ( prod ((fun _ => var -> T _) sigma_1) ((fun _ => var -> T _) sigma_2) ) .. ) ((fun _ => var -> T _) sigma_n)) _ => p) (pair ( .. (pair sigma_1 sigma_2) ..) sigma_n)) s) *)
(*   (at level 2, left associativity, *)
(*    format "s '[ ' .[ ( sigma_1 ; sigma_2 ;  .. ;  sigma_n ')' ] ']'") : msubst_scope. *)


Notation "s .[ sigma ]" :=  (subst sigma s)
  (at level 2, left associativity,
   format "s '[ ' .[ sigma ] ']'") : msubst_scope.


Delimit Scope msubst_scope with msubst.
Open Scope msubst_scope.


Section Classes.

  Context {sort : Type}
          {dec_eq_sort : forall a b : sort, Dec (a = b)}.
  Context {Vector_sort : Vector sort}.

  Context (term : sort -> Type).
  
  Context {VarConstr_term : VarConstr term} {Rename_term : Rename term} {Subst_term : Subst term}.
  
  Definition upren (o : sort) (xi : sort -> var -> var) : sort -> var -> var :=
    upd o (0 .: (xi o >>> S)) xi.
  Global Arguments upren o xi o' x/.

  Definition idr : sort -> var -> var := fun _ => id.
  
  Definition ren (xi : sort -> var -> var) := newV (xi >>2 ids).

  Definition up (o : sort) (sigma : substitution term) : substitution term :=
    updV o (ids o 0 .: getV sigma o >>> rename (upd o (+1) idr) (o := _)) (sigma |>> rename (upd o (+1) idr)).
  Global Arguments up o sigma : simpl never.

  
  Lemma up_comp_ren_subst o xi sigma :
    up o (newV (xi >>2 getV sigma)) = newV (upren o xi >>2 getV (up o sigma)).
  Proof.
    unfold up. unfold updV. f_equal. f_ext. intros o'. f_ext. simpl.
    unfold funcompV. unfold mapV. rewrite ?getV_newV.
    unfold upd.
    decide (o=o'); simpl.
    - unfold eq_rect_r. unfold eq_rect. destruct eq_sym. now intros [|x].
    - now intros [|x].
Qed.  

Lemma up_comp_ren_subst_n o xi sigma n :
  iterate (up o) n (newV (xi >>2 getV sigma)) = newV (iterate (upren  o) n xi >>2 getV (iterate (up o) n sigma)) .
Proof.
  induction n. reflexivity. rewrite !iterate_S, IHn. apply up_comp_ren_subst.
Qed.
  
 Class SubstLemmas  :=
    {
      rename_subst (xi : sort -> var -> var) (o : sort) (s : term o) :
        rename xi s = subst (ren xi) s;
      subst_id (o : sort) (s : term o) :
        s.[newV ids] = s;
      id_subst (sigma : substitution term) (o : sort) (x : var) :
        (ids o x).[sigma] = getV sigma o x;
      subst_comp (sigma tau : substitution term) (o : sort) (s : term o) :
        s.[sigma].[tau] = s.[sigma |>> subst tau]
    }.
  
End Classes.
Arguments up {sort dec_eq_sort Vector_sort term VarConstr_term Rename_term} o sigma : simpl never.
Arguments ren {sort Vector_sort term VarConstr_term} xi : simpl never.
Arguments SubstLemmas {sort Vector_sort} term {VarConstr_term Rename_term Subst_term}.

Arguments idr {sort} o/ x. 

Arguments newV : simpl never.
Arguments getV {sort Vector T} !v o.
Arguments funcompV {sort Vector_sort term} !v f. 
    
Inductive sort := Ty | Ter.

Instance decide_eq_sort (o1 o2 : sort) : Dec (o1 = o2). gen_Dec_eq. Defined.

Instance Vector_sort : Vector sort :=
  {
    vec := (fun T => T Ty * T Ter)%type;
    getV T v := let (v1, v2) := v in
               fun o => match o with
                         | Ty => v1
                         | Ter => v2
                       end;
    newV T f := (f Ty, f Ter)
  }.
Proof. intros. f_ext. now destruct 0. Defined.

Inductive term : sort -> Type :=
| VarC  (o : sort) (x : var) : term o
| Arr    (A B : term Ty) : term Ty
| All    (A : {bind Ty in (term Ty)}) : term Ty
| Abs    (A : term Ty) (s : {bind Ter in term Ter}) : term Ter
| App    (s t : term Ter) : term Ter
| TAbs   (s : {bind Ty in term Ter}) : term Ter
| TApp   (s : term Ter) (A : term Ty) : term Ter.

Instance VarConstr_term : VarConstr term := VarC.

Ltac derive_Rename :=
  match goal with [ |- Rename ?term ] =>
    hnf; fix inst 3; change _ with (Rename term) in inst;
    intros xi o s; change (annot (term o) s); destruct s;
    match goal with
      | [ x : var |- annot _ (?VarC _ _)] => exact (VarC o (xi o x))
      | [ |- annot _ ?t ] =>
        let rec map s :=
            (match s with
               | ?s1 ?s2 =>
                 let s1 := map s1 in
                 let T  := typeof s2 in
                 let s2 :=
                     match T with
                       | term _ => constr:(rename xi s2)
                       | var  => constr:(xi s2)
                       | @_bind _ ?o _ 1 => constr:(rename (upren o xi) s2)
                       | @_bind _ ?o _ ?n =>
                           constr:(rename (iterate (upren o) n xi) s2)
                       | _ => s2
                     end in
                 constr:(s1 s2)
               | _ => s
             end) in
        let t := map t in exact t
    end
  end.

Hint Extern 0 (Rename _) => derive_Rename : derive.


Instance Rename_term : Rename term. derive_Rename. Show Proof. Defined.

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

Ltac derive_Subst :=
  match goal with [ |- Subst ?term ] =>
    require_instance (Rename term);
    hnf; fix inst 3; change _ with (Subst term) in inst;
    intros sigma o s; change (annot (term o) s); destruct s;
    match goal with
      | [ x : var |- annot _ (?VarC _ _)] => 
        exact (getV sigma o x)
      | [ |- annot _ ?t ] =>
        let rec map s :=
            (match s with
               | ?s1 ?s2 =>
                 let s1 := map s1 in
                 let T  := typeof s2 in
                 let s2 :=
                   match T with
                     | term _ => constr:(s2.[sigma])
                     | _bind ?o _ 1 => constr:(s2.[up o sigma])
                     | _bind ?o _ ?n => constr:(s2.[iterate (up o) n sigma])
                   end in
                 constr:(s1 s2)
               | _ => s
             end) in
        let t := map t in exact t
    end
  end.
Hint Extern 0 (Subst _) => derive_Subst : derive.
Arguments eq_rect_r {A x} P H {y} H0/.

Definition foo I := Subst (Vector_sort := I) term.

Instance Subst_term : Subst term.
derive. Show Proof. Defined.

Goal forall (a : var -> term Ty) (b : var -> term Ter), (subst (a,b) (ids Ter 0)) = (ids Ter 0).[pair a b]. trivial. Qed.

Lemma iter_param {A B} (f : A -> A) (g : B -> B) (h : A -> B) :
  (forall x, g (h x) = h (f x)) ->
  (forall x n, iterate g n (h x) = h (iterate f n x)).
Proof.
  intros E x n. induction n. reflexivity. now rewrite !iterate_S, IHn, E.
Qed.

Require Import FunctionalExtensionality.

Ltac casedist_up := intros o; intros; simpl; destruct o; unfold up; unfold ren; unfold newV; unfold funcompV; simpl; f_equal; f_ext; (intros [|x]); reflexivity.

Lemma up_comp_subst_ren_n_internal :
  (forall o sigma xi, up o (sigma |>> rename xi) = up o sigma |>> rename (upren o xi))->
  (forall o sigma xi n,
    iterate (up o) n (sigma |>> rename xi) = iterate (up o) n sigma |>> rename (iterate (upren o) n xi)).
Proof.
  intros E o sigma xi n. induction n. reflexivity. rewrite !iterate_S, IHn.
  apply E.
Qed.

Ltac derive_SubstLemmas :=
  lazymatch goal with
    [ |- 
@SubstLemmas ?sort ?Vector_sort ?term ?VarConstr_term ?Rename_term ?Subst_term] =>

    (* rename subst *)

assert (rename_subst :
          forall o xi (s : term o), rename xi s = subst (ren xi) s)
  by (
      assert (up_upren :
                forall o xi, up o (ren xi) = ren (upren o xi))
      by casedist_up;
      assert (up_upren_n :
                forall o xi n, iterate (up o) n (ren xi) = ren (iterate (upren o) n xi))
        by (intros; now apply iter_param);
      fix ih 3; intros o xi s; destruct s; (try destruct o); try reflexivity; try (simpl; f_equal ;
                                                                                  try apply mmap_ext; intros; rewrite ?up_upren, ?up_upren_n; now apply ih));

  (* subst id *)

  assert (subst_id : forall o (s : term o), subst (newV ids) s = id s)
  by (
      assert (up_id : forall o, up o (newV ids) = newV ids) by casedist_up;
      assert (up_id_n : forall o n, iterate (up o) n (newV ids) = (newV ids)) by (intros; now apply iter_fp);
      fix ih 2; intros o s; destruct s; simpl in *; repeat match goal with [o : sort |- _ ] => destruct o end; f_equal; try reflexivity;
      rewrite ?up_id, ?up_id_n; try apply mmap_id_ext; intros; apply ih);
  
  (* subst comp *)
  
  assert (ren_subst_comp :
            forall (xi : sort -> var -> var) sigma o (s : term o), (rename xi s).[sigma] = s.[newV (xi >>2 getV sigma)])
    by (
        fix ih 4; intros xi sigma o s; destruct s; simpl; trivial; try
        (now destruct o); now ( 
        f_equal; rewrite ?up_comp_ren_subst, ?up_comp_ren_subst_n, ?mmap_comp;
               try apply mmap_ext; intros; try apply ih)
      );
  
  assert (subst_ren_comp : forall sigma xi o (s : term o),
                             rename xi s.[sigma] = s.[sigma |>> rename xi])
    by (
        
        assert (up_comp_subst_ren :
                  forall o sigma xi, up o (sigma |>> rename xi) = up o sigma |>> rename (upren o xi))
        by (
            intros o sigma xi; destruct sigma; destruct o; simpl; unfold up; unfold funcompV; simpl; repeat first[f_ext | f_equal]; destruct 0; trivial; simpl; try now repeat rewrite rename_subst, ren_subst_comp);
        
        assert (up_comp_subst_ren_n :
                  forall o sigma xi n, iterate (up o) n (sigma |>> rename xi) = iterate (up o) n sigma |>> rename (iterate (upren o) n xi))
          by (
              apply up_comp_subst_ren_n_internal; apply up_comp_subst_ren);
        fix ih 4; intros sigma xi o s; destruct s; try reflexivity; simpl;
        f_equal; rewrite ?up_comp_subst_ren, ?up_comp_subst_ren_n, ?mmap_comp;
        first [now destruct o | intros; apply ih]                          
      );
  
assert (subst_comp :
          forall o sigma tau (s : term o), s.[sigma].[tau] = s.[sigma |>> subst tau])
  by (
      assert (up_comp : forall o sigma tau, up o (sigma |>> subst tau) = up o sigma |>> subst (up o tau))
      by (
          intros o sigma tau; destruct o; unfold up; unfold funcompV; simpl;
          repeat first[f_ext | f_equal] ;
          destruct 0; simpl; trivial; rewrite ?subst_ren_comp; now rewrite ?ren_subst_comp
        );
      
      (* assert (up_comp_n : forall sigma tau n, upn n (sigma >> tau) = upn n sigma >> upn n tau) *)
      (*  by (apply up_comp_n_internal; apply up_comp); *)
      fix ih 4; intros o sigma tau s; destruct s; simpl; trivial; simpl; f_equal;
      rewrite ?up_comp, (*?up_comp_n, *) ?mmap_comp;
      try apply mmap_ext; intros; solve[ now destruct o | apply ih]
    );
constructor; hnf; intros;
[apply rename_subst|apply subst_id|reflexivity|apply subst_comp]
  end.
Hint Extern 0 (SubstLemmas _) => derive_SubstLemmas : derive.


Instance SubstLemmas_term : SubstLemmas term.
 derive. Qed.
  


(** **** Call-by value reduction *)


Inductive eval : term Ter -> term Ter -> Prop :=
| eval_beta (A : term Ty) (s t u1 u2 v : term Ter) :
    eval s (Abs A u1) -> eval t u2 -> eval (u1.[(ids Ty, u2 .: ids Ter)]) v -> eval (App s t) v
| eval_tbeta (B : term Ty) (s A v : term Ter) :
    eval s (TAbs A) -> eval A.[(B .: ids Ty, ids Ter)] v -> eval (TApp s B) v
| eval_abs (A : term Ty) (s : term Ter) :
    eval (Abs A s) (Abs A s)
| eval_tabs (A : term Ter) :
    eval (TAbs A) (TAbs A).
Hint Resolve eval_abs eval_tabs.



(** Derived substitution lemmas. *)

Section LemmasForSubst.

  Context {sort : Type}
          {dec_eq_sort : forall a b : sort, Dec (a = b)}
          {Vector_sort : Vector sort}
          {term : sort -> Type}
          {VarConstr_term : VarConstr term} {Rename_term : Rename term} {Subst_term : Subst term}
          {SubstLemmas_term : SubstLemmas term}.

Implicit Types (sigma tau theta :  substitution term) (xi : sort -> var -> var).

Lemma rename_substX xi : rename xi = subst (ren xi).
Proof. repeat(f_ext; intros). now apply rename_subst. Qed.

(* Variable (o : sort) (sigma : vec (fun o : sort => var -> term o)) (s : term o) . *)

(* Goal up o sigma = up o sigma. unfold up. simpl. rewrite rename_substX. simpl. *)

Lemma upX o (sigma : substitution term) :
  up o sigma =
  updV o (ids o 0 .: getV sigma o >>> subst (ren (upd o (+1) idr)) (o:=o))
     (sigma |>> subst (ren (upd o (+1) idr))).
Proof. unfold up. now rewrite rename_substX. Qed.

Lemma id_scompX sigma o : ids o >>> subst sigma (o := o) = getV sigma o.
Proof. f_ext. now eapply id_subst. Qed.

Lemma id_scompR {A} sigma o (f : term o -> A) :
  ids o >>> (subst sigma (o := o) >>> f) = getV sigma o >>> f.
Proof. now rewrite <- compA, id_scompX. Qed.

Lemma subst_idX : subst (newV ids) = fun o (s : term o) => s.
Proof. f_ext. intro. f_ext. now eapply subst_id. Qed.

Lemma subst_compI sigma tau o (s : term o) :
  s.[sigma].[tau] = s.[sigma |>> subst tau].
Proof. now eapply subst_comp. Qed.

Lemma subst_compX sigma tau o :
  subst sigma (o := o) >>> subst tau (o := o) = subst (sigma |>> subst tau) (o := o).
Proof. f_ext. intro. now eapply subst_comp. Qed.

(* Lemma subst_compR {A} sigma tau (f : _ -> A) : *)
(*   subst sigma >>> (subst tau >>> f) = subst (sigma >>> subst tau) >>> f. *)
(* Proof. now rewrite <- subst_compX. Qed. *)

Lemma fold_ren_cons (x : var) (xi : var -> var) o :
  ids o x .: (xi >>> ids o) = (x .: xi) >>> ids o.
Proof. now rewrite scons_comp. Qed.

(* unfold upn *)

(* Lemma upnSX n sigma : *)
(*   upn (S n) sigma = ids 0 .: upn n sigma >>> subst (ren (+1)). *)
(* Proof. *)
(*   unfold iterate; now rewrite upX. *)
(* Qed. *)

(* Lemma upnSE n sigma : *)
(*   upn (S n) sigma = ids 0 .: upn n sigma >> ren (+1). *)
(* Proof. *)
(*   now rewrite upnSX. *)
(* Qed. *)

(* Lemma upn0 sigma : upn 0 sigma = sigma. *)
(* Proof. reflexivity. Qed. *)



(* fold up *)

(* Lemma fold_up k sigma : *)
(*   ids k .: sigma >> ren (+S k) = up sigma >> ren (+k). *)
(* Proof. *)
(*   unfold scomp, ren. rewrite upX; fsimpl; rewrite id_subst, subst_compX; simpl; fsimpl. *)
(*   unfold ren. fsimpl. rewrite id_scompX. now fsimpl. *)
(* Qed. *)

(* Lemma fold_up0 sigma : *)
(*   sigma >> ren (+0) = sigma. *)
(* Proof. *)
(*   unfold scomp, ren. fsimpl. now rewrite subst_idX. *)
(* Qed. *)



(* combine up *)

(* Lemma fold_up_up sigma : up (up sigma) = upn 2 sigma. *)
(* Proof. reflexivity. Qed. *)

(* Lemma fold_up_upn n sigma : up (upn n sigma) = upn (S n) sigma. *)
(* Proof. reflexivity. Qed. *)

(* Lemma fold_upn_up n sigma : upn n (up sigma) = upn (S n) sigma. *)
(* Proof. now rewrite iterate_Sr. Qed. *)

End LemmasForSubst.


Ltac autosubst_typeclass_normalize :=
  mmap_typeclass_normalize;
  repeat match goal with
  | [|- context[ids ?x]] =>
    let s := constr:(ids x) in progress change (ids x) with s
  | [|- appcontext[ren ?xi]] =>
    let s := constr:(ren xi) in progress change (ren xi) with s
  | [|- appcontext[rename ?xi]] =>
    let s := constr:(rename xi) in progress change (rename xi) with s
  | [|- appcontext[subst ?sigma]] =>
    let s := constr:(subst sigma) in progress change (subst sigma) with s
  end.

Ltac autosubst_typeclass_normalizeH H :=
  mmap_typeclass_normalizeH H;
  repeat match typeof H with
  | context[ids ?x] =>
    let s := constr:(ids x) in progress change (ids x) with s in H
  | appcontext[ren ?xi] =>
    let s := constr:(ren xi) in progress change (ren xi) with s in H
  | appcontext[rename ?xi] =>
    let s := constr:(rename xi) in progress change (rename xi) with s in H
  | appcontext[subst ?sigma] =>
    let s := constr:(subst sigma) in progress change (subst sigma) with s in H
  end.


Ltac autosubst_unfold_up :=
  rewrite ?upX (*, ?upnSX; *)
  (* repeat match goal with *)
  (* | [|- context[upn 0 ?sigma]] => change (upn 0 sigma) with sigma *)
  (* end *).

Ltac autosubst_unfold_upH H :=
  rewrite ?upX(* , ?upnSX*) in H(*; *)
  (* repeat match typeof H with *)
  (* | context[upn 0 ?sigma] => change (upn 0 sigma) with sigma *)
  (* end *).

Ltac autosubst_unfold :=
  autosubst_typeclass_normalize; autosubst_unfold_up;
  rewrite ?(@rename_substX _ _ _ _ _ _); unfold ren, upren.

Ltac autosubst_unfoldH H :=
  autosubst_typeclass_normalizeH H; autosubst_unfold_upH H;
  rewrite ?(@rename_substX _ _ _ _ _ _) in H; unfold ren, upren in H.

Ltac etaReduce := repeat lazymatch goal with [|- context[fun x => ?f x]] => change (fun x => f x) with f end.

Ltac etaReduceH H := repeat lazymatch goal with [H : context[fun x => ?f x] |- _ ] => change (fun x => f x) with f in H end.

Ltac asimpl :=
  let subst_idX_inst := fresh "E" in
  lazymatch goal with [|- appcontext[@subst _ _ _ ?Subst_term]] =>
pose proof (@subst_idX _ _ _ _ _ Subst_term _) as subst_idX_inst;
  unfold newV in subst_idX_inst;
  simpl in subst_idX_inst
  end; 
  simpl; autosubst_unfold; repeat first
  [ progress (
      simpl; unfold _bind, ren, funcompV; fsimpl; autosubst_unfold_up;
      autorewrite with autosubst;
      rewrite ?id_scompX, ?id_scompR, ?subst_compX,
      (* ?subst_compR, *) ?id_subst, ?subst_id, ?subst_compI, ?subst_idX_inst
      (* repeat match goal with [|- appcontext[@subst ?sort ?vec ?term ?Subst ?sigma]] => *)
      (*                        replace (@subst sort vec term Subst sigma ) with (fun o : sort =>  @id (term o)) by eauto using subst_idX end *)
    )
  | fold_id];
(* fold_ren; fold_comp; fold_up *)
  clear subst_idX_inst
.

Ltac asimplH H :=
  simpl in H; autosubst_unfoldH H; repeat first
  [ progress (
        simpl in H;
        unfold _bind, ren, funcompV in H; fsimplH H;
        autosubst_unfold_upH H;
        autorewrite with autosubst in H;
        rewrite ?id_scompX, ?id_scompR, ?subst_compX,
        (* ?subst_compR, *) ?id_subst, ?subst_id in H;
        repeat setoid_rewrite subst_compI in H;
        let E := constr:(@subst_idX _ _ _ _ _ _) in rewrite ?(E _ _) in H (* I have no idea why this works ... well, it does no longer in Coq 8.5*)
      )
  | fold_idH H](* ; *)
(* fold_ren; fold_comp; fold_up *).

Lemma eta {A : Type} (f : var -> A): (fun b : var => f b) = f. reflexivity. Qed.

Lemma eval_subst s t : eval s t -> forall (sigma : var -> term Ty) (tau : var -> term Ter) , eval s.[(sigma, tau)] t.[(sigma, tau)].
Proof.
  simpl.
  induction 1; intros; eauto using eval.
  - econstructor; eauto.
    fsimpl. asimpl.
    specialize (IHeval3 sigma tau).
    asimplH IHeval3.
    assumption.
  - econstructor; eauto. asimpl.
    specialize (IHeval2 sigma tau).
    asimplH IHeval2.
    assumption.
Qed.

(** **** Syntactic typing *)

Definition ctx := list (term Ty)
.
Inductive has_type (Gamma : ctx) : term -> type -> Prop :=
| ty_var (x : var) :
    x < size Gamma -> has_type Gamma (TeVar x) Gamma`_x
| ty_abs (A B : type) (s : term) :
    has_type (A :: Gamma) s B ->
    has_type Gamma (Abs A s) (Arr A B)
| ty_app (A B : type) (s t : term) :
    has_type Gamma s (Arr A B) ->
    has_type Gamma t A ->
    has_type Gamma (App s t) B
| ty_tabs (A : type) (s : term) :
    has_type Gamma..[ren (+1)] s A ->
    has_type Gamma (TAbs s) (All A)
| ty_tapp (A B : type) (s : term) :
    has_type Gamma s (All A) ->
    has_type Gamma (TApp s B) A.[B/].

(** **** Semantic typing *)

Definition L (P : term -> Prop) (s : term) :=
  exists2 v, eval s v & P v.

Fixpoint V (A : type) (rho : var -> term -> Prop) (v : term) {struct A} : Prop :=
  match A with
    | TyVar X => eval v v /\ rho X v
    | Arr A B => exists A' : type, exists2 s : term, v = Abs A' s &
        forall u, V A rho u -> L (V B rho) s.[u/]
    | All A => exists2 s : term, v = TAbs s &
        forall i (B : type), L (V A (i .: rho)) s.|[B/]
  end.
Notation E A rho := (L (V A rho)).

Lemma V_value A rho v : V A rho v -> eval v v.
Proof. by elim: A => [x[]|A _ B _/=[A'[s->]]|A _/=[s->]]. Qed.
Hint Resolve V_value.

Lemma V_to_E A rho v : V A rho v -> E A rho v.
Proof. exists v; eauto. Qed.
Hint Resolve V_to_E.

Lemma eq_V A rho1 rho2 v :
  (forall X v, eval v v -> (rho1 X v <-> rho2 X v)) -> V A rho1 v -> V A rho2 v.
Proof.
  elim: A rho1 rho2 v => //=.
  - move=> x rho1 rho2 v eqn [ev /eqn]. by intuition.
  - move=> A ih1 B ih2 rho1 rho2 v eqn [A' [s -> h]]. exists A'.
    exists s=>// u /ih1/h[]. by move=> X w; split; apply eqn.
    move=> w ev /ih2 ih. by exists w; eauto.
  - move=> A ih rho1 rho2 v eqn [s->h]. exists s => // P B.
    case: (h P B) => u ev /ih va. exists u => //. apply: va => -[|X] //=.
    exact: eqn.
Qed.

Lemma V_ren A rho s xi :
  V A.[ren xi] rho s <-> V A (xi >>> rho) s.
Proof.
  elim: A rho s xi => //=.
  - move=> A ih1 B ih2 rho v xi. split=> -[A'[s->h]];
     (do 2 eexists) => // t /ih1/h[u ev]/ih2 ih; by exists u.
  - move=> A ih rho s xi; asimpl.
    split=> -[s' -> h]; eexists => //; asimpl=> P B; move: {h} (h P B) => [v ev].
    + move=> /ih {ih} ih. exists v => //. by asimpl in ih.
    + move=> h. exists v => //. apply/ih. autosubst.
Qed.

Lemma E_ren A rho s xi :
  E A.[ren xi] rho s <-> E A (xi >>> rho) s.
Proof.
  split=> -[v ev /V_ren h]; by exists v.
Qed.

Lemma V_subst A rho v sigma :
  V A.[sigma] rho v <-> V A (fun x => V (sigma x) rho) v.
Proof.
  elim: A rho v sigma.
  - move=> x rho v sigma /=. split; intuition eauto.
  - move=> A ih1 B ih2 rho v sigma /=. split=> -[A' [s->h]];
      (do 2 eexists) => // t /ih1/h[u ev]/ih2 ih; by exists u.
  - move=> A ih rho v sigma. split;
      asimpl; move=> [s->{v}h]; eexists=> [//|P B].
    + move: (h P B) => [v ev /ih hv]. exists v => //.
      apply: eq_V hv => -[|X] //= u. by intuition. move=> _. asimpl. exact: V_ren.
    + move: (h P B) => [v ev hv]. exists v => //. apply/ih.
      apply: eq_V hv => -[|X] //= u. by intuition. asimpl.
      split => [p|/V_ren//]. by apply/V_ren.
Qed.

Definition VG (Gamma : ctx) (rho : var -> term -> Prop) (sigma : var -> term) :=
  forall x, x < size Gamma -> E Gamma`_x rho (sigma x).

Theorem soundness Gamma s A :
  has_type Gamma s A ->
    forall delta sigma rho, VG Gamma rho sigma -> E A rho s.|[delta].[sigma].
Proof.
  elim=> {Gamma s A} [Gamma x xe|Gamma A B s _ ih|Gamma A B s t _ ih1 _ ih2|
                      Gamma A s _ ih|Gamma A B s _ ih] delta sigma rho l.
  - exact: l.
  - eexists; first by autosubst. (do 2 eexists)=> [//|t vt]. asimpl.
    apply: ih=> -[_/=|x/l//]. exact: V_to_E.
  - case: (ih1 delta _ _ l) => {ih1} /= v ev1 [A' [u eq ih1]]; subst v.
    case: (ih2 delta _ _ l) => {ih2} v ev2 ih2.
    case: (ih1 _ ih2) => {ih1} w ev3 ih1. exists w => //.
    exact: eval_beta ev1 ev2 ev3.
  - apply: V_to_E. eexists=> [//=|P B]. asimpl. apply: ih => x /=.
    rewrite size_map => wf. rewrite get_map //. apply/E_ren. exact: l.
  - move: (ih delta _ _ l) => [v ev1 {ih} /=[s' eq ih]]; subst v.
    specialize (ih (V B rho) B.[delta]). move: ih => [v ev2 ih]. exists v.
    exact: eval_tbeta ev1 ev2. apply/V_subst. apply: eq_V ih => -[|x] //=.
    by intuition.
Qed.

(** **** Applications *)

Definition nilA : var -> term -> Prop := fun _ _ => False.

Corollary soundness_nil s A :
  has_type [::] s A -> E A nilA s.
Proof.
  move=> h. cut (E A nilA s.|[ids].[ids]). autosubst. exact: (soundness h).
Qed.

Corollary normalization s A :
  has_type [::] s A -> exists v, eval s v.
Proof.
  move=> /soundness_nil[v hv] _. by exists v.
Qed.

Corollary consistency s :
  ~has_type [::] s (All (TyVar 0)).
Proof.
  move=> /soundness_nil[v _ /= [t {s v} _ /(_ (fun _ => False) (TyVar 0))]].
  by move=> [s {t} _ []].
Qed.