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

Lemma wp_server_session (db c : term) (alist : gmap term term): 
cryptis_ctx -∗
channel c -∗
AList.is_alist db (repr <$> alist) -∗
WP Server.session db c
{{ x , True }}.
Proof.
  iIntros "#Cryptis #Hc Hdb".
  wp_lam. wp_pures.
  wp_apply (wp_recv with "Hc").
  iIntros "%m1 #Hpubm1".
  wp_list_of_term m1; wp_pures.
  2: by iModIntro.
  do !rewrite subst_list_match /=.
  wp_list_match => [uid α X_u | _].
  2: wp_pures; by iModIntro.
  intro Hm1eq.
  wp_bind (AList.find _ _).
  iApply (AList.wp_find with "Hdb").
  iIntros "!> Hdb". rewrite lookup_fmap.
  case db_uid: (alist !! uid) => [file|]; wp_pures.
  2: by iModIntro.
  do !rewrite subst_list_match /=.
  clear db_uid.
  wp_list_of_term_eq file' e.
  2: wp_pures.
  2: by iModIntro.
  wp_pures.
  wp_list_match => [k_s p_s P_s P_u envelope _ | ].
  2: intro H; wp_pures.
  2: by iModIntro.
  wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => False)%I).
  1: iAssumption.
  iIntros "%x_s %Hnoncex_s #Hmintedx_s #Hprivatex_s #H!eqx_s Htokenx_s".
  wp_pures.
  wp_apply wp_texp. wp_pures.
  wp_apply wp_texp. wp_pures.
  wp_apply wp_ke.
  1: done.
  iIntros "_".
  wp_pures.
  wp_list.
  wp_apply wp_H.
  1: done.
  iIntros "_".
  wp_pures.
  unfold hash_result.
  wp_list.
  wp_apply wp_prf.
  1: done.
  iIntros "_".
  wp_pures.
  wp_list.
  wp_apply wp_prf.
  1: done.
  iIntros "_".
  unfold hash_result.
  wp_list.
  wp_term_of_list.
  wp_pures.
  rewrite Hm1eq.
  rewrite public_of_list /=.
  iDestruct "Hpubm1" as "[Hpubuid [Hpubα [HpubX_u _]]]".
  wp_apply wp_send.
  1: done.
  1: do !rewrite public_of_list /=.
  do !iSplit => //.
  iApply public_TExp => //.
  admit.
  iApply public_TExp_iff.
  intro contra. destruct contra.
  iRight.
  do !iSplit => //.
  by iApply minted_TInt.
  iApply "H!eqx_s". iNext. iModIntro. admit.
  admit.
  iApply public_THash.
  admit.
  wp_pures.
  wp_apply (wp_recv with "Hc").
  iIntros "%m3 #Hm3pub".
  wp_pures.
  wp_list.
  wp_apply wp_prf => //.
  iIntros "_".
  wp_eq_term Heq; wp_pures.
  2: by iModIntro.
  wp_list.
  wp_pures.
  by iModIntro.
Admitted.
  

End Opaque.
