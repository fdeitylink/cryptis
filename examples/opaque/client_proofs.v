From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib term cryptis primitives tactics.

From cryptis.examples Require Import alist.
From cryptis.examples.opaque Require Import impl shared.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Opaque.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ}.
Notation iProp := (iProp Σ).

Lemma wp_client_session (uid c pw : term): 
cryptis_ctx -∗
channel c -∗
public uid -∗
WP Client.session uid c pw
{{ x , True }}.
Proof.
  iIntros "#Cryptis #Hc #pubuid".
  wp_lam. wp_pures.
  wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => False)%I).
  1: iAssumption.
  iIntros "%x_u %Hnoncex_u #Hmintedx_u #Hprivatex_u #H!eqx_u Htokenx_u".
  wp_pures.
  wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => False)%I).
  1: iAssumption.
  iIntros "%r %Hnoncer #Hmintedr #Hprivater #H!eqr Htokenr".
  wp_pures.
  wp_apply wp_H'.
  1: done.
  iIntros "_".
  unfold hash_result.
  wp_apply wp_texp.
  wp_pures.
  wp_apply wp_texp.
  wp_pures.
  wp_list.
  wp_term_of_list.
  wp_pures.
  do !rewrite subst_list_match /=.
  wp_apply wp_send.
  1: done.
  do !rewrite public_of_list /=.
  do !iSplit => //.
  iApply public_TExp_iff.
  intro contra.
  destruct contra.
  iRight.
  do !iSplit => //.
  iApply minted_THash.
  iApply minted_tag.
  admit.
  iApply "H!eqr".
  iNext. iModIntro.
  admit.
  iApply public_TExp.
  by iApply public_g.
  admit.
  wp_pures.
  wp_apply wp_recv.
  1: done.
  iIntros "%m2 #pubm2".
  wp_list_of_term m2; wp_pures.
  2: done.
  wp_list_match => [β X_s envelope A_s | _].
  2: by wp_pures.
  intro Hm2eq.
  wp_pures.
Admitted.

End Opaque.
