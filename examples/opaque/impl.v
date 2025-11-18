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

Section Opaque.
  
Implicit Types N : namespace.

Local Existing Instance ticket_lock.

Notation dbN := (nroot.@"db").

Definition OPRF : val := λ: "H" "H'" "k",
    λ: "x", "H" ["x"; (texp ("H'" "x") "k")].

Definition KE : val := λ: "H" "p_a" "x_a" "P_b" "X_b",
    "H" [texp "P_b" "p_a" ; texp "X_b" "x_a"].

Definition make_file : val := λ: "H" "H'" "pw" "AuthEnc",
    let: "k_s" := #1 in (* TODO: random *)
    let: "rw" := (OPRF "H" "H'" "k_s") "pw" in
    let: "p_s" := #1 in (* TODO: random *)
    let: "p_u" := #1 in (* TODO: random *)
    let: "k_s" := #1 in (* TODO: random *)
    let: "P_s" := texp #0 "p_s" in
    let: "P_u" := texp #0 "p_u" in
    let: "c" := "AuthEnc" "rw" ["p_u"; "P_u"; "P_s"] in
    SOME ["k_s"; "p_s"; "P_s"; "P_u"; "c"].

Definition usr_session : val := λ: "H'" "pw",
    let: "r" := #1 (* TODO: random *) in
    let: "x_u" := #1 (* TODO: random *) in
    let: "α" := texp ("H'" "pw") in
    let: "X_u" := texp #0 "x_u" in
    SOME ["r"; "x_u"; (* pub-mark *) "α"; "X_u"].

Definition server_session : val
  := λ: "sid" "ssid" "H" "db" "prf" "α" "X_u",
    (* TODO: check α ∈ G *)
    match: AList.find "db" "sid" with
      NONE => NONE (* TODO: proper way to abort? *)
    | SOME "file" =>
        list_match: ["k_s"; "p_s"; "P_s"; "P_u"; "c"] := "file" in
        let: "x_s" := #1 (* TODO: random *) in
        let: "β" := texp "α" "k_s" in
        let: "X_s" := texp #0 "x_s" in
        let: "K" := "KE" "H" "p_s" "x_s" "P_u" "X_u" in
        let: "ssid'" := "H" ["sid" "ssid" "α"] in
        let: "SK" := "f" "K" #0 "ssid'" in
        let: "A_s" := "f" "K" #1 "ssid'" in
        SOME ["K"; "ssid'"; (* pub-mark *) "β"; "X_s"; "c"; "A_s"]
    end.

Definition user_receive : val
  := λ: "sid" "ssid" "H" "AuthDec" "prf" "pw" "r" "β" "X_s" "c" "A_s",
    (* TODO: check β ∈ G *)
    let: "rw" := "H" "pw" (texp "β" (hl_inv "r")) in
    match: "AuthDec" "rw" "c" with
      NONE => NONE (* TODO: proper way to abort? *)
    | SOME "l" =>
        list_match: ["p_u"; "P_u"; "P_s"] := "list" in
        let: "K" := KE "H" "p_u" "x_u" "P_s" "X_s" in
        let: "ssid'" := "H" ["sid"; "ssid"; "α"] in
        let: "SK" := "prf" "K" #0 "ssid'" in
        if: "A_s" = "prf" "K" #1 "ssid'" then
          let: "A_u" := "prf" "K" #2 "ssid'" in
          SOME ["sid"; "ssid"; "SK"; (* pub-mark *) "A_u"]
        else
          NONE (* TODO: proper way to abort? *)
    end.

Definition server_receive : val
  := λ: "sid" "ssid" "prf" "k" "ssid'" "SK" "A_u",
    if: "A_u" = "prf" "K" #2 "ssid'" then
      SOME ["sid"; "ssid"; "SK"]
    else
      NONE.

End Opaque.
