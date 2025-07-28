From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma perm_rem (T : eqType) (x : T) s1 s2 :
  perm_eq s1 s2 -> perm_eq (rem x s1) (rem x s2).
Proof.
move=> s1s2; apply/permP => P.
by rewrite !count_rem (permP s1s2) (perm_mem s1s2).
Qed.
