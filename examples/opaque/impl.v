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

Notation dbN := (nroot.@"db").

Definition OPRF : val := λ: "H" "H'" "k",
    λ: "x", "H" ["x"; (texp ("H'" "x") "k")].

Definition KE : val := λ: "H" "p_a" "x_a" "P_b" "X_b",
    "H" [texp "P_b" "p_a" ; texp "X_b" "x_a"].

(* TODO: use tags instead of literal ints to make SK private, but A_s and A_u public *)

(* rw needs to be wrapped in derive_senc *)

Module Client.

Section Client.

Definition user_session : val := λ: "g" "H'" "pw",
    let: "r" := mk_nonce #() in
    let: "x_u" := mk_nonce #() in
    let: "α" := texp ("H'" "pw") in
    let: "X_u" := texp "g" "x_u" in
    SOME ["r"; "x_u"; (* pub-mark *) "α"; "X_u"].

Definition user_receive : val
  := λ: "sid" "ssid" "H" "AuthDec" "prf" "pw" "r" "β" "X_s" "c" "A_s",
    (* TODO: check β ∈ G *)
    let: "rw" := "H" ["pw"; (texp "β" (hl_inv "r"))] in
    bind: "l" := "AuthDec" "rw" "c" in
      list_match: ["p_u"; "P_u"; "P_s"] := "list" in
        let: "K" := KE "H" "p_u" "x_u" "P_s" "X_s" in
        let: "ssid'" := "H" ["sid"; "ssid"; "α"] in
        let: "SK" := "prf" ["K"; #0; "ssid'"] in
        if: "A_s" = "prf" ["K"; #1; "ssid'"] then
          let: "A_u" := "prf" ["K"; #2; "ssid'"] in
          SOME ["sid"; "ssid"; "SK"; (* pub-mark *) "A_u"]
        else
          NONE.

(* TODO: do actual connections *)
Definition user_flow : val
  := λ: "sid" "ssid" "g" "H" "H'" "prf" "AuthEnc" "AuthDec" "pw",
    list_match: ["r"; "x_u"; (* pub-mark *) "α"; "X_u"] := user_session "g" "H'" "pw" in
      send-thing ["α"; "X_s"] ;;
      list_match: ["β"; "X_s"; "c"; "A_s"] := receive-thing in
        bind: "user_data" := user_receive "sid" "ssid" "H" "AuthDec" "prf" "pw" "r" "β" "X_s" "c" "A_s" in
          list_match: ["sid"; "ssid"; "SK"; (* pub-mark *) "A_u"] := "user_data" in
            send-thing "A_u" ;;
            SOME ["sid"; "ssid"; "SK"].

End Client.

End Client.

Module Server.

Section Server.

(* not useful: assume that files in db are properly formed instead *)
(* but maybe use this as an example?  that the files can be computed. *)
Definition make_file : val := λ: "g" "H" "H'" "AuthEnc" "pw",
    let: "k_s" := mk_nonce #() in
    let: "rw" := (OPRF "H" "H'" "k_s") "pw" in
    let: "p_s" := mk_nonce #() in
    let: "p_u" := mk_nonce #() in
    let: "P_s" := texp "g" "p_s" in
    let: "P_u" := texp "g" "p_u" in
    let: "c" := "AuthEnc" "rw" ["p_u"; "P_u"; "P_s"] in
    SOME ["k_s"; "p_s"; "P_s"; "P_u"; "c"].

Definition server_session : val
  := λ: "sid" "ssid" "g" "H" "db" "prf" "α" "X_u",
    (* TODO: check α ∈ G *)
    bind: "file" := AList.find "db" "sid" in
      list_match: ["k_s"; "p_s"; "P_s"; "P_u"; "c"] := "file" in
        let: "x_s" := mk_nonce #() in
        let: "β" := texp "α" "k_s" in
        let: "X_s" := texp "g" "x_s" in
        let: "K" := "KE" "H" "p_s" "x_s" "P_u" "X_u" in
        let: "ssid'" := "H" ["sid" "ssid" "α"] in
        let: "SK" := "prf" ["K"; #0; "ssid'"] in
        let: "A_s" := "prf" ["K"; #1; "ssid'"] in
        SOME ["K"; "ssid'"; (* pub-mark *) "β"; "X_s"; "c"; "A_s"].

Definition server_receive : val
  := λ: "sid" "ssid" "prf" "k" "ssid'" "SK" "A_u",
    if: "A_u" = "prf" ["K"; #2; "ssid'"] then
      SOME ["sid"; "ssid"; "SK"]
    else
      NONE.

(* OPRF and KE defined entirely in terms of other variables: defined elsewhere *)
(* TODO: do actual connections *)
(* enforce that other side is consistently the same person *)
Definition server_flow : val
  := λ: "sid" "ssid" "g" "H" "H'" "prf" "AuthEnc" "AuthDec" "db",
    list_match: ["α"; "X_u"] := receive-thing in
      bind: "session_data" := server_session "sid" "ssid" "g" "H" "db" "prf" "α" "X_u" in
        list_match: ["K"; "ssid'"; (* pub-mark *) "β"; "X_s"; "c"; "A_s"] := "session_data" in
          send-thing ["β"; "X_s"; "c"; "A_s"] ;;
          let: "A_u" := receive-thing in
          server_receive "sid" "ssid" "prf" "k" "ssid'" "SK" "A_u".

End Server.

End Server.
