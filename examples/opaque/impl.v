From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import proofmode.

From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import lock ticket_lock.
From cryptis Require Import lib term cryptis primitives tactics rpc.
From cryptis.examples Require Import alist.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Implicit Types N : namespace.

Local Existing Instance ticket_lock.

Notation opN := (nroot.@"op").

Definition _H : string -> val := fun tag => (λ: "val", hash (tag (Tag $ opN.@tag) "val"))%V.
Definition prf  := _H.
Definition H    := _H.
Definition H'   := _H.

Definition OPRF : val := λ: "k",
    λ: "x", H "rw" ["x"; (texp ((H' "α") "x") "k")].

(* TODO: use the key exchange formula from the OPAQUE paper *)
Definition KE : val := λ: "p_a" "x_a" "P_b" "X_b",
    H "K" [texp "P_b" "p_a" ; texp "X_b" "x_a"].

Module Client.

Section Client.

(* TODO: sid/ssid source? *)
Definition client_session : val := λ: "g" "sid" "ssid" "c" "pw",
    let: "x_u" := mk_nonce #() in
    let: "r" := mk_nonce #() in
    let: "α" := texp (H' "α" "pw") "r" in
    let: "X_u" := texp "g" "x_u" in
    let: "m1" := term_of_list [ "sid"; "ssid"; "α"; "X_u" ] in
    send "c" "m1" ;;
    bind: "m2" := list_of_term (recv "c") in
    list_match: [ "β"; "X_s"; "envelope"; "A_s" ] := "m2" in
    (* TODO: check β ∈ G *)
    let: "rw" := derive_senc (H "rw" [ "pw"; (texp "β" (hl_inv "r")) ]) in
    bind: "envelope_dec" := adec "rw" (* TODO: envelope tag *) "envelope" in
    list_match: [ "p_u"; "P_u"; "P_s" ] := "envelope_dec" in
    let: "K" := KE "H" "p_u" "x_u" "P_s" "X_s" in
    let: "ssid'" := H "ssid'" ["sid"; "ssid"; "α"] in
    let: "SK" := prf "SK" [ "K"; "ssid'" ] in
    guard: "A_s" = prf "A_s" [ "K"; "ssid'" ] in
    let: "A_u" := prf "A_u" [ "K"; "ssid'" ] in
    let: "m3" := term_of_list [ "c"; "A_u" ] in
    send "m3" ;;
    SOME [ "sid"; "ssid"; "SK" ].

End Client.

End Client.

Module Server.

Section Server.

(* OPRF and KE defined entirely in terms of other variables: defined elsewhere *)
(* enforce that other side is consistently the same person *)
Definition server_session : val := λ: "g" "db" "c",
    bind: "m1" := list_of_term (recv "c") in
    list_match: [ "sid"; "ssid"; "α"; "X_u" ] := "m1" in
    (* TODO: check α ∈ G *)
    bind: "file" := AList.find "db" "sid" in
    list_match: [ "k_s"; "p_s"; "P_s"; "P_u"; "envelope" ] := "file" in
    let: "x_s" := mk_nonce #() in
    let: "β" := texp "α" "k_s" in
    let: "X_s" := texp "g" "x_s" in
    let: "K" := KE "p_s" "x_s" "P_u" "X_u" in
    let: "ssid'" := H "ssid'" [ "sid"; "ssid"; "α" ] in
    let: "SK" := prf "SK" [ "K"; "ssid'" ] in
    let: "A_s" := prf "A_s" [ "K"; "ssid'" ] in
    let: "m2" := term_of_list [ "β"; "X_s"; "envelope"; "A_s" ] in
    send "c" "m2" ;;
    bind: "m3" := list_of_term (recv "c") in
    list_match: [ "c"; "A_u" ] := "m3" in
    guard: "A_u" = prf "A_u" [ "K"; "ssid'" ] in
    SOME [ "sid"; "ssid"; "SK" ].

(* not useful: assume that files in db are properly formed instead *)
(* but maybe use this as an example?  that the files can be computed. *)
Definition make_file : val := λ: "g" "AuthEnc" "pw",
    let: "k_s" := mk_nonce #() in
    let: "rw" := OPRF "k_s" "pw" in
    let: "p_s" := mk_nonce #() in
    let: "p_u" := mk_nonce #() in
    let: "P_s" := texp "g" "p_s" in
    let: "P_u" := texp "g" "p_u" in
    let: "c" := "AuthEnc" "rw" ["p_u"; "P_u"; "P_s"] in
    SOME ["k_s"; "p_s"; "P_s"; "P_u"; "c"].

End Server.

End Server.
