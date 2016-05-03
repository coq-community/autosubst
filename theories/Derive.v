(** Tactics to generate substitution operations and show the basic lemmas. *)
From Autosubst Require Import Basics MMap Classes Tactics Decidable.

(* Ltac app_var := match goal with [ |- var] => assumption end. *)

(* Ltac derive_VarConstr := intro;  solve *)
(*   [ constructor 1; [app_var] | constructor 2; [app_var] *)
(*   | constructor 3; [app_var] | constructor 4; [app_var] *)
(*   | constructor 5; [app_var] | constructor 6; [app_var] *)
(*   | constructor 7; [app_var] | constructor 8; [app_var] *)
(*   | constructor 9; [app_var] | constructor 10; [app_var] *)
(*   | constructor 11; [app_var] | constructor 12; [app_var] *)
(*   | constructor 13; [app_var] | constructor 14; [app_var] *)
(*   | constructor 15; [app_var] | constructor 16; [app_var] *)
(*   | constructor 17; [app_var] | constructor 18; [app_var] *)
(*   | constructor 19; [app_var] | constructor 20; [app_var]]. *)
(* Hint Extern 0 (VarConstr _) => derive_VarConstr : derive. *)


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
                     | term _ => constr:(s2.|[sigma])
                     | _bind ?o _ 1 => constr:(s2.|[up o sigma])
                     | _bind ?o _ ?n => constr:(s2.|[iterate (up o) n sigma])
                   end in
                 constr:(s1 s2)
               | _ => s
             end) in
        let t := map t in exact t
    end
  end.
Hint Extern 0 (Subst _) => derive_Subst : derive.


Lemma mmap_id_ext {A B} {inst : MMap A B} `{@MMapLemmas A B inst}
  `{@MMapExt A B inst} (f : A -> A) (b : B) :
  (forall x, f x = x) -> mmap f b = b.
Proof. intros E. rewrite (mmap_ext E). apply mmap_id. Defined.

Lemma iter_fp {A} (f : A -> A) x :
  f x = x -> forall n, iterate f n x = x.
Proof.
  intros E. induction n. reflexivity. rewrite iterate_S. simpl. now rewrite IHn.
Qed.

Lemma iter_param {A B} (f : A -> A) (g : B -> B) (h : A -> B) :
  (forall x, g (h x) = h (f x)) ->
  (forall x n, iterate g n (h x) = h (iterate f n x)).
Proof.
  intros E x n. induction n. reflexivity. rewrite !iterate_S. simpl. now rewrite IHn, E.
Qed.

Ltac casedist_up := intros o; intros; simpl; destruct o; unfold up; unfold renV; unfold newV; unfold funcompV; simpl; f_equal; f_ext; (intros [|x]); reflexivity.

Section SubstLemmasInternal.

  Context {sort : Set} {decide_eq_sort : forall a b : sort, Dec (a = b)} {Vector_sort : Vector sort}.
  Context {term : sort -> Type}
          {VarConstr_term : VarConstr term} {Rename_term : Rename term} {Subst_term : Subst term}
          {SubstLemmas_term : SubstLemmas term}.

Lemma up_comp_subst_ren_n_internal :
  (forall o sigma xi, up o (sigma |>> rename xi) = up o sigma |>> rename (upren o xi))->
  (forall o sigma xi n,
    iterate (up o) n (sigma |>> rename xi) = iterate (up o) n sigma |>> rename (iterate (upren o) n xi)).
Proof.
  intros E o sigma xi n. induction n. reflexivity. rewrite !iterate_S. simpl. now rewrite IHn.
Qed.

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
  induction n. reflexivity. rewrite !iterate_S. simpl. rewrite IHn. apply up_comp_ren_subst.
Qed.

End SubstLemmasInternal.

Ltac derive_SubstLemmas :=
  lazymatch goal with
    [ |-
@SubstLemmas ?sort ?Vector_sort ?term ?VarConstr_term ?Rename_term ?Subst_term] =>

    (* rename subst *)

assert (rename_subst :
          forall o xi (s : term o), rename xi s = subst (renV xi) s)
  by (
      assert (up_upren :
                forall o xi, up o (renV xi) = renV (upren o xi))
      by casedist_up;
      assert (up_upren_n :
                forall o xi n, iterate (up o) n (renV xi) = renV (iterate (upren o) n xi))
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
