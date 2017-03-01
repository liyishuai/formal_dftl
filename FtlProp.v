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


(*  -------------------------------------------------------------

  Predicates for block no.

*)
Definition bvalid_logical_page_no (lpn: page_no) := blt_nat lpn (MAX_LOGICAL_BLOCKS * PAGES_PER_BLOCK).

Definition bvalid_logical_block_no (lbn: block_no) := blt_nat lbn MAX_LOGICAL_BLOCKS.

Definition valid_block_no (pbn: block_no):Prop := bvalid_block_no pbn = true.

Definition valid_page_no (ppn: page_no):Prop := bvalid_page_no ppn = true.

Definition valid_logic_block_no (lbn:block_no) :Prop := bvalid_logical_block_no lbn = true.

Definition valid_logic_page_no (lpn:page_no) :Prop := bvalid_logical_page_no lpn = true.

Definition valid_page_off (off: page_off):Prop := bvalid_page_off off = true.

Lemma valid_page_off_dec :
  forall off,
    valid_page_off off \/ ~ valid_page_off off.
Proof.
  intros.
  unfold valid_page_off.
  destruct (bvalid_page_off off).
  left; trivial.
  right.
  auto.
Qed.


(*  -------------------------------------------------------------

  Predicates for page state table

*)
Definition pst_domain_is_complete (pst: page_state_table) : Prop :=
  list_len pst  = PAGES_PER_BLOCK.

Definition pst_page_state (pst:page_state_table) (b:block) :Prop :=
  forall loc,
    valid_page_off loc
    -> match pst_get pst loc with
           | Some (ps_data lpn) => exists p,block_get_page b loc = Some p /\
                                          page_state p = ps_programmed /\ 
                                          (exists lbn loff,page_oob p = Some (lbn,loff) /\
                                                           lpn = lbn * PAGES_PER_BLOCK + loff)
           | Some (ps_trans gtd_loc) => exists p,block_get_page b loc = Some p /\
                                          page_state p = ps_programmed /\ 
                                          (exists gtd_loc',page_oob p = Some (gtd_loc',0) /\
                                                           gtd_loc  =  gtd_loc')
           | Some ps_erased => exists p,block_get_page b loc = Some p /\
                                          page_state p = ps_free
           | _ => True
       end.
  
Definition pst_shape (pst: page_state_table) (np: page_off) : Prop :=
  forall loc,
    valid_page_off loc
    -> (blt_nat loc np = false 
        -> pst_get pst loc  = Some ps_erased)  
       /\ (blt_nat loc np =  true 
           -> ~pst_get pst loc = Some ps_erased).

Definition predicate_pst (pst:page_state_table) (b:block) : Prop :=
  pst_domain_is_complete pst /\ pst_page_state pst b.

(*  -------------------------------------------------------------

  Predicates for "block info"
  Mark: Now ignore the (oob)
*)

Definition block_coherent_data (bi:block_info) (b:block) :Prop :=
    bi_state bi = bs_data /\
    block_state b = bs_programmed /\
    bi_used_pages bi = next_page b /\
    (forall loc,
       valid_page_off loc
       -> exists p, block_get_page b loc = Some p /\
                    page_state p = ps_programmed).

Definition block_coherent_trans (bi:block_info) (b:block) :Prop :=
    bi_state bi = bs_trans /\
    block_state b = bs_programmed /\
    bi_used_pages bi = next_page b /\
    (forall loc,
       valid_page_off loc
       -> exists p, block_get_page b loc = Some p /\
                    page_state p = ps_programmed).

Definition block_coherent_erased (bi:block_info) (b:block) :Prop :=
    bi_state bi = bs_erased /\
    block_state b = bs_free /\
    bi_used_pages bi = next_page b /\
    bi_used_pages bi = 0 /\
    (forall loc,
       valid_page_off loc
       -> exists p, block_get_page b loc = Some p /\
                    page_state p = ps_free).

Definition block_coherent_partial (loc: page_off) (b: block): Prop :=
  next_page b = loc
  /\ block_state b = bs_programmed
  /\ (forall off,
        valid_page_off off
        -> (blt_nat off loc = true
            -> exists p, block_get_page b off = Some p
                         /\ page_state p = ps_programmed)
           /\ (blt_nat off loc = false
               -> exists p, block_get_page b off = Some p
                            /\ page_state p = ps_free)).

Definition chip_bi_coherent (c:chip) (pbn:block_no) (bi:block_info) :=
  exists b,chip_get_block c pbn = Some b
           /\ match (bi_state bi) with
                  | bs_erased => block_coherent_erased bi b
                  | bs_invalid => True
                  | bs_data   => block_coherent_data bi b /\ (exists pst ,bi_page_state bi = pst /\ predicate_pst pst b) 
                  | bs_trans  => block_coherent_trans bi b /\ (exists pst ,bi_page_state bi = pst /\ predicate_pst pst b)
               end.

(*  -------------------------------------------------------------

  Predicates for free block queue

*)

Definition pbn_in_fbq (fbq: block_queue) (pbn: block_no) : Prop :=
  fbq_in fbq pbn = true.

Definition pbn_not_in_fbq (fbq: block_queue) (pbn: block_no) : Prop :=
  fbq_in fbq pbn = false.

