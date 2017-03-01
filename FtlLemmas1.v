Require Import LibEx.
Require Import bnat.
Require Import List.
Require Import ListEx.
Require Import Data.

Require Import Params.
Require Import Nand.
Require Import Dftl2.

Require Import Framework.
Require Import Inv.

Lemma Inv_ftl_init: forall c f ,fld_init = Some (c,f) -> Inv c f.
Proof.
Admitted.

Lemma ftl_read_init_i