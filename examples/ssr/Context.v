(* Support for dependent contexts with the right reduction behaviour. *)
Require Import Autosubst.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Definition get {T} `{Ids T} (Gamma : seq T) (n : var) : T :=
  nth (ids 0) Gamma n.
Arguments get {T _} Gamma n.

Fixpoint dget {T} `{Ids T} `{Subst T} (Gamma : list T) (n : var) {struct n} : T :=
  match Gamma, n with
    | [::], _ => ids 0
    | A :: _, 0 => A.[ren (+1)]
    | _ :: Gamma, n.+1 => (dget Gamma n).[ren (+1)]
  end.
Arguments dget {T _ _} Gamma n.

Lemma get_map {T} `{Ids T} (f : T -> T) Gamma n :
  n < size Gamma -> get (map f Gamma) n = f (get Gamma n).
Proof. exact: nth_map. Qed.

Definition equivariant {T1 T2} `{Ids T1} `{Ids T2} `{Subst T1} `{Subst T2}
  (f : T1 -> T2) := forall (x : T1) (xi : var -> var), (f x).[ren xi] = f x.[ren xi].

Lemma dget_map {T} `{Ids T} `{Subst T} (f : T -> T) Gamma n :
  equivariant f -> n < size Gamma -> dget (map f Gamma) n = f (dget Gamma n).
Proof.
  elim: n Gamma => [|n ih] [|A Gamma] //= ev lt. by rewrite ih.
Qed.


