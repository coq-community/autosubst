(** * Context

    Support for dependent contexts with the right reduction behaviour. *)
From Coq Require Import ssreflect ssrfun ssrbool Lists.List.
Require Import AutosubstSsr.

Definition get {T} `{!Ids T} (Gamma : list T) (n : var) : T :=
  nth n Gamma (ids 0).
Arguments get {T _} Gamma n.

Fixpoint dget {T} `{!Ids T, !Subst T} (Gamma : list T) (n : var) {struct n} : T :=
  match Gamma, n with
    | nil, _ => ids 0
    | A :: _, 0 => A.[ren (+1)]
    | _ :: Gamma, (S n) => (dget Gamma n).[ren (+1)]
  end.
Arguments dget {T _ _} Gamma n.

Lemma get_map {T} `{Ids T} (f : T -> T) Gamma n :
  n < length Gamma -> get (map f Gamma) n = f (get Gamma n).
Proof.
  rewrite -(map_length f).
  intros Hn. rewrite /get. etransitivity.
  2:{ apply map_nth. }
  by apply nth_indep.
Qed.

(* Local Variables: *)
(* coq-load-path: (("." "Ssr")) *)
(* End: *)
