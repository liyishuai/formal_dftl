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
Require Import FTLLemmas2.

Lemma bit_update_spec:forall bit pbn,valid_block_no pbn -> 
                                 exists bi,bit_get bit pbn = Some bi. 
Proof.
skip.
Qed.

Lemma invalid_old_page_spec:forall bit pbn off,exists bit',invalid_old_page bit pbn off = Some bit'.
Proof.
skip.
Qed.