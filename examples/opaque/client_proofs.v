From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import proofmode.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Opaque.

Context `{!heapGS Σ, !cryptisG Σ, !sessionG Σ}.
Notation iProp := (iProp Σ).

End Opaque.
