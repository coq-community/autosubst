(** Tactics to generate substitution operations and show the basic lemmas. *)
Require Import Autosubst_Basics Autosubst_MMap Autosubst_Classes Autosubst_Tactics Autosubst_Lemmas.

Ltac app_var := match goal with [ |- var] => assumption end.

Ltac derive_Ids := intro;  solve
  [ constructor 1; [app_var] | constructor 2; [app_var]
  | constructor 3; [app_var] | constructor 4; [app_var]
  | constructor 5; [app_var] | constructor 6; [app_var]
  | constructor 7; [app_var] | constructor 8; [app_var]
  | constructor 9; [app_var] | constructor 10; [app_var]
  | constructor 11; [app_var] | constructor 12; [app_var]
  | constructor 13; [app_var] | constructor 14; [app_var]
  | constructor 15; [app_var] | constructor 16; [app_var]
  | constructor 17; [app_var] | constructor 18; [app_var]
  | constructor 19; [app_var] | constructor 20; [app_var]].
Global Hint Extern 0 (Ids _) => derive_Ids : derive.

Ltac derive_Rename :=
  let inst := fresh "dummy" in (* hack/workaround *)
  match goal with [ |- Rename ?term ] =>
    hnf; fix inst 2; change _ with (Rename term) in inst;
    intros xi s; change (annot term s); destruct s;
    match goal with
      | [ |- annot _ ?t ] =>
        let rec map s :=
            (match s with
               | ?s1 ?s2 =>
                 let s1 := map s1 in
                 let T  := typeof s2 in
                 let s2 :=
                     match T with
                       | term => constr:(rename xi s2)
                       | var  => constr:(xi s2)
                       | _bind term _ 1 => constr:(rename (upren xi) s2)
                       | _bind term _ ?n =>
                           constr:(rename (iterate upren n xi) s2)
                       | context[_bind term _ 1] =>
                           constr:(mmap (rename (upren xi)) s2)
                       | context[_bind term _ ?n] =>
                           constr:(mmap (rename (iterate upren n xi)) s2)
                       | context[term] => constr:(mmap (rename xi) s2)
                       | _ => s2
                     end in
                 constr:(s1 s2)
               | _ => s
             end) in
        let t := map t in exact t
    end
  end.
Global Hint Extern 0 (Rename _) => derive_Rename : derive.

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
  let inst := fresh "dummy" in (* hack/workaround *)
  match goal with [ |- Subst ?term ] =>
    require_instance (Rename term);
    hnf; fix inst 2; change _ with (Subst term) in inst;
    intros sigma s; change (annot term s); destruct s;
    match goal with
      | [ |- annot _ ?t ] =>
        let rec map s :=
            (match s with
               | ?s1 ?s2 =>
                 let s1 := map s1 in
                 let T  := typeof s2 in
                 let s2 :=
                   match T with
                     | term => constr:(subst sigma s2)
                     | _bind term _ 1 => constr:(subst (up sigma) s2)
                     | _bind term _ ?n => constr:(subst (upn n sigma) s2)
                     | _bind ?hterm _ ?n =>
                         constr:(subst (sigma >>| (ren(+n) : var -> hterm)) s2)
                     | context[_bind term _ 1] =>
                         constr:(mmap (subst (up sigma)) s2)
                     | context[_bind term _ ?n] =>
                         constr:(mmap (subst (upn n sigma)) s2)
                     | context[_bind ?hterm _ ?n] =>
                         constr:(mmap
                                   (subst (sigma >>| (ren(+n) : var -> hterm)))
                                   s2)
                     | context[term] => constr:(mmap (subst sigma) s2)
                     | _ => s2
                   end in
                 constr:(s1 s2)
               | _ => s
             end) in
        match has_var t with
          | Some ?x => exact (sigma x)
          | _ => let t := map t in exact t
        end
    end
  end.
Global Hint Extern 0 (Subst _) => derive_Subst : derive.

Ltac derive_HSubst :=
  let inst := fresh "dummy" in (* hack/workaround *)
  match goal with [ |- HSubst ?inner ?outer ] =>
    require_instance (Subst inner);
    hnf; fix inst 2; change _ with (HSubst inner outer) in inst;
    intros sigma s; change (annot outer s); destruct s;
    match goal with
      | [ |- annot _ ?t ] =>
        let rec map s :=
            (match s with
               | ?s1 ?s2 =>
                 let s1 := map s1 in
                 let T  := typeof s2 in
                 let s2 :=
                   match T with
                     | inner => constr:(subst sigma s2)
                     | outer => constr:(hsubst sigma s2)
                     | _bind inner outer 1 => constr:(hsubst (up sigma) s2)
                     | _bind inner inner 1 => constr:(subst (up sigma) s2)
                     | _bind inner outer ?n =>
                         constr:(hsubst (upn n sigma) s2)
                     | _bind inner inner ?n =>
                         constr:(subst (upn n sigma) s2)
                     | _bind _     outer _ => constr:(hsubst sigma s2)
                     | _bind _     inner _ => constr:(subst sigma s2)
                     | context[_bind inner outer 1] =>
                         constr:(mmap (hsubst (up sigma)) s2)
                     | context[_bind inner inner 1] =>
                         constr:(mmap (subst (up sigma)) s2)
                     | context[_bind inner outer ?n] =>
                         constr:(mmap (hsubst (upn n sigma)) s2)
                     | context[_bind inner inner ?n] =>
                         constr:(mmap (subst (upn n sigma)) s2)
                     | context[_bind _     outer _] =>
                         constr:(mmap (hsubst sigma) s2)
                     | context[_bind _     inner _] =>
                         constr:(mmap (subst sigma) s2)
                     | context[inner] => constr:(mmap (subst sigma) s2)
                     | context[outer] => constr:(mmap (hsubst sigma) s2)
                     | _ => s2
                   end in
                 constr:(s1 s2)
               | _ => s
             end) in
        let t := map t in exact t
    end
  end.
Global Hint Extern 0 (HSubst _ _) => derive_HSubst : derive.

Lemma mmap_id_ext {A B} {inst : MMap A B} `{@MMapLemmas A B inst}
  `{@MMapExt A B inst} (f : A -> A) (b : B) :
  (forall x, f x = x) -> mmap f b = b.
Proof. intros E. rewrite (mmap_ext E). apply mmap_id. Defined.

Lemma iter_fp {A} (f : A -> A) x :
  f x = x -> forall n, iterate f n x = x.
Proof.
  intros E. induction n. reflexivity. now rewrite iterate_S, IHn.
Qed.

Lemma iter_param {A B} (f : A -> A) (g : B -> B) (h : A -> B) :
  (forall x, g (h x) = h (f x)) ->
  (forall x n, iterate g n (h x) = h (iterate f n x)).
Proof.
  intros E x n. induction n. reflexivity. now rewrite !iterate_S, IHn, E.
Qed.

Section InternalLemmas.

Context {term : Type} {Ids_term : Ids term}
  {Rename_term : Rename term} {Subst_term : Subst term}.

Lemma up_upren_internal :
  (forall xi x, rename xi (ids x) = ids (xi x)) ->
  (forall xi : var -> var, up (ren xi) = ren (upren xi)).
Proof.
  intros E xi. f_ext. intros [|x]. reflexivity. apply E.
Qed.

Lemma up_upren_n_internal :
  (forall xi, up (ren xi) = ren (upren xi)) ->
  (forall xi n, upn n (ren xi) = ren (iterate upren n xi)).
Proof.
  apply (iter_param upren up (fun x => ren x)).
Qed.

Lemma up_id_internal :
  (forall xi x, rename xi (ids x) = ids (xi x)) ->
  up ids = ids :> (var -> term).
Proof.
  intros h. f_ext. intros [|x]. reflexivity. apply h.
Qed.

Lemma up_id_n_internal :
  up ids = ids -> (forall n, upn n ids = ids).
Proof.
  apply iter_fp.
Qed.

Lemma up_comp_ren_subst xi (sigma : var -> term) :
  up (xi >>> sigma) = upren xi >>> up sigma.
Proof. f_ext. intros [|x]; reflexivity. Qed.

Lemma up_comp_ren_subst_n xi (sigma : var -> term) n :
  upn n (xi >>> sigma) = iterate upren n xi >>> upn n sigma.
Proof.
  induction n. reflexivity. rewrite !iterate_S, IHn. apply up_comp_ren_subst.
Qed.

Lemma up_comp_subst_ren_internal :
  (forall xi x, rename xi (ids x) = ids (xi x)) ->
  (forall xi s, rename xi s = s.[ren xi]) ->
  (forall xi sigma s, (rename xi s).[sigma] = s.[xi >>> sigma]) ->
  (forall sigma xi, up (sigma >>> rename xi) = up sigma >>> rename (upren xi)).
Proof.
  intros h1 h2 h3 sigma xi. f_ext. intros [|x]. unfold up; simpl.
  now rewrite h1. unfold up. simpl. now rewrite h2, h3, h2, h3.
Qed.

Lemma up_comp_subst_ren_n_internal :
  (forall sigma xi, up (sigma >>> rename xi) = up sigma >>> rename (upren xi))->
  (forall (sigma : var -> term) xi n,
    upn n (sigma >>> rename xi) = upn n sigma >>> rename (iterate upren n xi)).
Proof.
  intros E sigma xi n. induction n. reflexivity. rewrite !iterate_S, IHn.
  apply E.
Qed.

Lemma up_comp_internal :
  (forall sigma x, (ids x).[sigma] = sigma x) ->
  (forall xi sigma s, (rename xi s).[sigma] = s.[xi >>> sigma]) ->
  (forall sigma xi s, rename xi s.[sigma] = s.[sigma >>> rename xi]) ->
  (forall sigma tau, up (sigma >> tau) = up sigma >> up tau).
Proof.
  intros h1 h2 h3 sigma tau. f_ext. intros [|x]; unfold up; simpl.
  now rewrite h1. now rewrite h2, h3.
Qed.

Lemma up_comp_n_internal :
  (forall sigma tau, up (sigma >> tau) = up sigma >> up tau) ->
  (forall sigma tau n,
    upn n (sigma >> tau) = upn n sigma >> upn n tau).
Proof.
  intros h sigam tau n. induction n. reflexivity. rewrite !iterate_S, IHn.
  apply h.
Qed.

End InternalLemmas.

Section InternalLemmasHSubst.

Context {inner : Type} {Ids_inner : Ids inner}
  {Rename_inner : Rename inner} {Subst_inner : Subst inner}
  {SubstLemmas_inner : SubstLemmas inner}.

Context {outer : Type} {Ids_outer : Ids outer}
  {Rename_outer : Rename outer} {HSubst_inst : HSubst inner outer}
  {HSubstLemmas_inst : HSubstLemmas inner outer}.

Implicit Types (sigma : var -> outer) (theta : var -> inner) (s : outer).

Lemma up_hcomp_internal :
  (forall xi theta s, rename xi s.|[theta] = (rename xi s).|[theta]) ->
  (forall sigma theta, up (sigma >>| theta) = up sigma >>| theta).
Proof.
  intros E sigma theta. f_ext. intros [|x]; unfold up; simpl.
  now rewrite id_hsubst. apply E.
Qed.

Lemma up_hcomp_n_internal :
  (forall sigma theta, up (sigma >>| theta) = up sigma >>| theta) ->
  forall sigma theta n, upn n (sigma >>| theta) = upn n sigma >>| theta.
Proof.
  intros E sigma theta n. induction n. reflexivity.
  rewrite !iterate_S, IHn. apply E.
Qed.

Lemma hcomp_lift_n_internal sigma theta n :
  (sigma >>| theta) >>| ren (+n) = (sigma >>| ren (+n)) >>| upn n theta.
Proof.
  f_ext. intros x; simpl. now rewrite !hsubst_comp, up_liftn.
Qed.

Lemma hcomp_lift_internal sigma theta :
  (sigma >>| theta) >>| ren (+1) = (sigma >>| ren (+1)) >>| up theta.
Proof. apply hcomp_lift_n_internal. Qed.

Context {Subst_outer : Subst outer}
  {SubstHSubstComp_inst : SubstHSubstComp inner outer}.

Lemma hcomp_ren_internal sigma xi theta :
  (forall xi s, rename xi s = s.[ren xi]) ->
  (sigma >>> rename xi) >>| theta = (sigma >>| theta) >>> rename xi.
Proof.
  intros E. f_ext. intros x. simpl. rewrite !E, subst_hsubst_comp.
  f_equal. f_ext. intros y. simpl. now rewrite id_hsubst.
Qed.

Lemma hcomp_dist_internal sigma tau theta :
  (sigma >> tau) >>| theta = (sigma >>| theta) >> (tau >>| theta).
Proof.
  f_ext. intros x. simpl. apply subst_hsubst_comp.
Qed.

End InternalLemmasHSubst.

Ltac derive_SubstLemmas :=
  let ih := fresh "dummy" in (* hack/workaround *)
  match goal with
    [ |- @SubstLemmas ?term ?Ids_term ?Rename_term ?Subst_term] =>
    let rename := constr:(@rename term Rename_term) in
    let subst := constr:(@subst term Subst_term) in
    let ids := constr:(@ids term Ids_term) in
    let up := constr:(@up term Ids_term Rename_term) in

    (* rename subst *)

    assert (rename_subst :
              forall xi (s : term), rename xi s = subst (ren xi) s) by (
     assert (up_upren :
               forall xi, up (ren xi) = ren (upren xi)) by
       (apply up_upren_internal; reflexivity);
     assert (up_upren_n :
               forall xi n, upn n (ren xi) = ren (iterate upren n xi)) by
       (apply up_upren_n_internal, up_upren);
     fix ih 2; intros xi s; destruct s; try reflexivity; simpl; f_equal;
     try apply mmap_ext; intros; rewrite ?up_upren, ?up_upren_n; apply ih);

    (* subst id *)

    assert (subst_id : forall (s : term), subst ids s = id s) by (
     assert (up_id : up ids = ids) by
       (apply up_id_internal; reflexivity);
     assert (up_id_n : forall n, upn n ids = ids) by
       (apply up_id_n_internal, up_id);
     fix ih 1; intros s; destruct s; simpl; f_equal; try reflexivity;
     rewrite ?up_id, ?up_id_n; try apply mmap_id_ext; intros; apply ih);

    (* subst comp *)

    assert (ren_subst_comp :
       forall xi sigma (s : term), (rename xi s).[sigma] = s.[xi >>> sigma]) by(
     fix ih 3; intros xi sigma s; destruct s; try reflexivity; simpl; f_equal;
     rewrite ?up_comp_ren_subst, ?up_comp_ren_subst_n, ?mmap_comp;
     try apply mmap_ext; intros; apply ih);

    assert (subst_ren_comp : forall sigma xi (s : term),
      rename xi s.[sigma] = s.[sigma >>> rename xi]) by (
     assert (up_comp_subst_ren :
      forall sigma xi, up (sigma >>> rename xi) = up sigma >>>rename (upren xi))
      by (apply up_comp_subst_ren_internal; [reflexivity|
          apply rename_subst| apply ren_subst_comp]);
     assert (up_comp_subst_ren_n :
      forall sigma xi n, upn n (sigma >>> rename xi) = upn n sigma >>> rename (iterate upren n xi))
      by (apply up_comp_subst_ren_n_internal; apply up_comp_subst_ren);
     fix ih 3; intros sigma xi s; destruct s; try reflexivity; simpl;
     f_equal; rewrite ?up_comp_subst_ren, ?up_comp_subst_ren_n, ?mmap_comp;
     try (rewrite hcomp_ren_internal; [|apply rename_subst]);
     try apply mmap_ext; intros; apply ih);

    assert (subst_comp :
          forall sigma tau (s : term), s.[sigma].[tau] = s.[sigma >> tau]) by (
     assert (up_comp : forall (sigma tau : var -> term), up (sigma >> tau) = up sigma >> up tau)
      by (apply up_comp_internal; [reflexivity|apply ren_subst_comp|apply subst_ren_comp]);
     assert (up_comp_n : forall sigma tau n, upn n (sigma >> tau) = upn n sigma >> upn n tau)
      by (apply up_comp_n_internal; apply up_comp);
     fix ih 3; intros sigma tau s; destruct s; try reflexivity; simpl; f_equal;
     rewrite ?up_comp, ?up_comp_n, ?mmap_comp, ?hcomp_dist_internal;
     try apply mmap_ext; intros; apply ih);

  constructor; hnf;
    [apply rename_subst|apply subst_id|reflexivity|apply subst_comp]
  end.
Global Hint Extern 0 (SubstLemmas _) => derive_SubstLemmas : derive.

Ltac derive_HSubstLemmas :=
  let ih := fresh "dummy" in (* hack/workaround *)
  match goal with [|- HSubstLemmas ?inner ?outer ] =>
  let ids := constr:(ids : var -> inner) in

  assert (hsubst_id : forall (s : outer), s.|[ids] = s) by (
    fix ih 1; intros s; destruct s; try reflexivity; simpl; f_equal;
    rewrite ?up_id, ?up_id_n; try apply mmap_id_ext; intros;
    (apply subst_id || apply ih)
  );

  assert (hsubst_comp : forall (theta eta : var -> inner) (s : outer),
    s.|[theta].|[eta] = s.|[theta >> eta])
  by (
    fix ih 3; intros sigma tau s; destruct s; try reflexivity; simpl; f_equal;
    rewrite <- ?up_comp, <- ?up_comp_n, ?mmap_comp; try apply mmap_ext; intros;
    (apply subst_comp || apply ih)
  );

  constructor; hnf; [exact hsubst_id|reflexivity|exact hsubst_comp]
  end.
Global Hint Extern 0 (HSubstLemmas _ _) => derive_HSubstLemmas : derive.

Ltac derive_SubstHSubstComp :=
  let ih := fresh "dummy" in (* hack/workaround *)
  match goal with [|- SubstHSubstComp ?inner ?outer ] => hnf;

  assert (ren_hsubst_comp : forall xi (theta : var -> inner) (s : outer),
    rename xi s.|[theta] = (rename xi s).|[theta]
  ) by (
    fix ih 3; intros xi theta s; destruct s; try reflexivity; simpl; f_equal;
    rewrite ?mmap_comp; try apply mmap_ext; intros; simpl; apply ih
  );

  assert (up_hcomp : forall (sigma : var -> outer) (theta : var -> inner),
    up (sigma >>| theta) = up sigma >>| theta
  ) by (
    apply up_hcomp_internal; apply ren_hsubst_comp
  );

  assert (up_hcomp_n : forall (sigma : var -> outer) (theta : var -> inner) n,
    upn n (sigma >>| theta) = upn n sigma >>| theta
  ) by (
    apply up_hcomp_n_internal; apply up_hcomp
  );

  fix ih 3; intros sigma tau s; destruct s; try reflexivity; simpl; f_equal;
  rewrite ?up_hcomp, ?up_hcomp_n, ?hcomp_lift_n_internal, ?mmap_comp;
  try apply mmap_ext; intros; apply ih
  end.
Global Hint Extern 0 (SubstHSubstComp _ _) => derive_SubstHSubstComp : derive.

(* Local Variables: *)
(* coq-load-path: (("." "Autosubst")) *)
(* End: *)
