From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang.lib Require Import assert.

From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import lock ticket_lock.
From cryptis.examples Require Import alist.

From cryptis.examples.opaque Require Import impl.
From cryptis Require Import primitives.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ, !sessionGS Σ, !metaGS Σ}.
Notation iProp := (iProp Σ).

Notation opN := (nroot.@"op").

Definition game : val :=
λ: <>,
let: "c" := init_network #() in
let: "sid" := mk_nonce #() in
let: "ssid" := mk_nonce #() in
let: "pw" := mk_nonce #() in
let: "db" := AList.new #() in
AList.insert "db" "sid" (Server.make_file "pw") ;;
Fork (Server.server_session "sid" "ssid" "db" "c");;
Client.client_session "sid" "ssid" "c" "pw";;
assert: (~ eq_term "pw" (recv "c")).

End Game.
