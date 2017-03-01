(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(*   Author: Yu Guo <aciclo@gmail.com>                                        *)
(*                                        Computer Science Department, USTC   *)
(*                                                                            *)
(*          Bihong Zhang <sa614257@mail.ustc.edu.cn                           *)
(*                                        School of Software Engineer, USTC   *)
(*                                                                            *)
(* ************************************************************************** *)

Require Import List.
Require Import ListEx.
Require Import Data.

Require Import Params.
Require Import Nand.
Require Import Dftl2.
Require Import FtlProp.
Section INV.

  Variable bit : block_info_table.
  Variable fbq : list block_no.
  Variable gtd:  global_mapping_directory.
  Variable cmt:  cache_mapping_table.

Definition bvalid_logical_page_no (lpn: page_no) := blt_nat lpn (MAX_LOGICAL_BLOCKS * PAGES_PER_BLOCK).

Definition bvalid_logical_block_no (lbn: block_no) := blt_nat lbn MAX_LOGICAL_BLOCKS.

Definition valid_block_no (pbn: block_no):Prop := bvalid_block_no pbn = true.

Definition valid_page_no (ppn: page_no):Prop := bvalid_page_no ppn = true.

Definition valid_logic_block_no (lbn:block_no) :Prop := bvalid_logical_block_no lbn = true.

Definition valid_logic_page_no (lpn:page_no) :Prop := bvalid_logical_page_no lpn = true.

Definition valid_page_off (off: page_off):Prop := bvalid_page_off off = true.


(* ## I1: every valid pbn has an item in the bit, and vice versa.  *)
Definition I_pbn_bit_valid := forall (pbn : block_no), 
                   valid_block_no pbn
                    <-> exists bi, bit_get bit pbn = Some bi.

(* ## I2a: The length of cmt is constant. *)
Definition I_length_cmt_const := list_len cmt = CMT_LENGTH.

(* ## I2b: The pbn number in the cmt is vaild and the block state is bs_data. 
And then the page state is data and the corrsoponding num is lpn
*)
Definition I_cmt_pbn_valid := forall loc record lpn pbn off flag,
                                   cmt_get cmt loc = Some record
                                   -> record = cmt_trans lpn pbn off flag
                                   -> (bvalid_logical_page_no lpn = true) /\ (valid_block_no pbn) 
                                     /\  (valid_page_off off) /\ (exists bi,bit_get bit pbn = Some bi /\ bi_state bi = bs_data 
                                     /\ (exists pst ,bi_page_state bi = pst /\ pst_get pst off = Some (ps_data lpn) ) ).

(* ## I2c: The block is in the cmt ,then mustn't in the fbq  *)
Definition I_cmt_pbn_not_fbq := forall loc record lpn pbn off flag,
                                   cmt_get cmt loc = Some record
                                   -> record = cmt_trans lpn pbn off flag
                                   -> fbq_in fbq pbn = false.

(* ## I3a: The length of gtd is constant. *)
Definition I_length_gtd_const := list_len gtd = GTD_LENGTH.

(* ## I3b: The pbn number in the cmt is vaild and the block state is bs_data. *)
Definition I_gtd_pbn_valid := forall loc record pbn off,
                                   gtd_get gtd loc = Some record
                                   -> record = gtd_trans pbn off
                                   -> (valid_block_no pbn) /\ (valid_page_off off)
                                      /\ (exists bi ,bit_get bit pbn = Some bi 
                                      /\ (bi_state bi = bs_trans) /\ ( exists pst ,bi_page_state bi = pst 
                                      /\ pst_get pst off = Some (ps_trans loc) ) ).
  
(* ## I3c: The block is in the gtd ,then mustn't in the fbq  *)
Definition I_gtd_pbn_not_fbq := forall loc record pbn off,
                                   gtd_get gtd loc = Some record
                                   -> record = gtd_trans pbn off
                                   -> fbq_in fbq pbn = false.

(* ## I4: every pbn in freebq is valid.*)
Definition I_pbn_fbq_valid := forall (pbn: block_no),
                    fbq_in fbq pbn = true
                    -> valid_block_no pbn. 

(* ## I5: every pbn in freebq is of "INVALID" or "ERASED" state.*)
Definition I_pbn_fbq_state := forall (pbn: block_no) bi,
                                fbq_in fbq pbn = true
                                -> bit_get bit pbn = Some bi 
                                -> bi_state bi = bs_invalid \/ bi_state bi = bs_erased.

(* ## I6: every two pbns in FREEBQ are different *)
Definition I_pbn_fbq_distinguishable:= forall i i' pbn pbn',
                     i <> i'
                     -> fbq_get fbq i = Some pbn
                     -> fbq_get fbq i' = Some pbn'
                     -> pbn <> pbn'.

(* ## I7: every lpn ,pbn, off in the translation page is valid *)
(* have some doubt *)
Definition I_pbn_trans_record_valid:= forall record lpn pbn off ,
                      record = trans_data lpn pbn off
                      -> valid_block_no pbn /\ valid_page_off off /\ bvalid_logical_page_no lpn = true.

Variable c:chip
.

Definition J_bi_block_coherent (c: chip) (bit: block_info_table) := 
  forall pbn bi, 
    bit_get bit pbn = Some bi
    -> chip_bi_coherent c pbn bi.

End INV.

Definition R_Inv (c: chip) (f: FTL) : Prop :=
  let bit := ftl_bi_table f in
  J_bi_block_coherent c bit.

Definition F_Inv (f:FTL) :  Prop :=
  let bit := ftl_bi_table f in
  let cmt := ftl_cmt_table f in
  let gtd := ftl_gtd_table f in
  let fbq := ftl_free_blocks f in 
    I_pbn_bit_valid bit
    /\ I_length_cmt_const cmt
    /\ I_cmt_pbn_valid bit cmt 
    /\ I_cmt_pbn_not_fbq fbq cmt 
    /\ I_length_gtd_const gtd
    /\ I_gtd_pbn_valid bit gtd
    /\ I_gtd_pbn_not_fbq fbq gtd
    /\ I_pbn_fbq_valid fbq
    /\ I_pbn_fbq_state bit fbq
    /\ I_pbn_fbq_distinguishable fbq
    /\ I_pbn_trans_record_valid.

Definition Inv (c: chip) (f: FTL) := 
  F_Inv f /\ R_Inv c f.
