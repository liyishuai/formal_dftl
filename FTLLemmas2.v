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

Lemma write_data_block_noemp :
  forall c f bit curdb_no curdb_bi poff lpn lbn off d,
    curdb_no = current_data_block f ->
    bit_get bit curdb_no = Some curdb_bi ->
    check_block_is_full curdb_bi = false ->
    poff = bi_used_pages curdb_bi ->
    valid_logic_page_no lpn ->
    lpn_to_lbn_off lpn = (lbn,off) ->
    exists c' bi' , write_data_block c curdb_bi curdb_no  poff d (Some (lbn,off)) (ps_data lpn) 
                                    = Some (c',bi') /\
                   (bi_used_pages bi' = bi_used_pages curdb_bi + 1) /\
                   bi_erase_count bi' = bi_erase_count curdb_bi /\
                   bi_state bi'= bi_state curdb_bi. 
Proof.
Admitted.