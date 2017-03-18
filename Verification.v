(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(*   Author: Yu Guo <guoyu@ustc.edu.cn>                                       *)
(*                          School of Computer Science and Technology, USTC   *)
(*                                                                            *)
(*           Bihong Zhang <sa614257@mail.ustc.edu.cn>                         *)
(*                                     School of Software Engineering, USTC   *)
(*                                                                            *)
(*           Yishuai Li <lyishuai@mail.ustc.edu.cn>                           *)
(*                                         School of the Gifted Young, USTC   *)
(*                                                                            *)
(* ************************************************************************** *)


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
Require Import FTLLemmas1.

Definition Inv (fld: flash_device) : Prop := 
  let (c, f) := fld in Inv.Inv c f.

Lemma valid_logic_page_no_iff: forall sec ,valid_logic_page_no sec <-> bvalid_sector_no sec = true.
Proof.
intros.
split.
intros.
unfold bvalid_sector_no.
unfold valid_logic_page_no in H.
assumption.
intros.
unfold bvalid_sector_no  in H.
unfold valid_logic_page_no.
assumption.
Qed.

Lemma R_init: forall ftl,fld_init = Some (nand_init,ftl) -> R hdd_init (nand_init,ftl) . 
Proof.
  intros.
  unfold R.
  intros.
  unfold hdd_read.
  destruct (bvalid_sector_no sec) eqn:HX.
  -
    unfold hdd_init.
    rewrite list_get_list_repeat_list.
    unfold fld_read.
    assert(HX1:valid_logic_page_no sec).
    {  
        unfold bvalid_sector_no  in HX.
        unfold valid_logic_page_no.
        unfold bvalid_logical_page_no.
        apply HX.
    }
    destruct (Ftl_read_init_spec sec ftl H HX1) as [c' HX2].
    rewrite HX2.
    unfold zero_page.
    simpl.
    reflexivity.
    +
      unfold bvalid_sector_no in HX.
      (* SearchAbout blt_nat. *)
      apply blt_true_lt.
      apply HX.
  -
    unfold fld_read.
    unfold FTL_read.
    assert (HX':Dftl2.bvalid_logical_page_no sec = false).
     apply HX.
    rewrite HX'.
    reflexivity.
Qed.

(* Lemma Inv_init: forall ftl,fld_init = Some (nand_init,ftl) -> R hdd_init (nand_init,ftl) .  *)

 
Lemma fld_write_R_prservation:
  forall fld hdd sec d hdd' fld',
  Inv fld ->
  R hdd fld ->
  hdd_write hdd sec d = Some hdd' ->
  fld_write fld sec d = Some fld' ->
  R hdd' fld'.
Proof.
unfold R.
intros.
destruct (beq_nat sec0 sec) eqn:HX.
-
  desbnat.
  destruct fld as [c f].
  destruct fld' as [c' f'].
  subst sec0.
  rewrite (hdd_read_write_at_same_addr hdd sec d hdd' H1).
  assert (HX:hdd_read hdd sec = fld_read (c,f) sec).
    {
      apply (H0 sec).
    }
  unfold fld_read.
  unfold fld_read in HX.
  (* TO DO*)
  skip.
-
  skip.
Qed.

Lemma fld_write_inv:
  forall fld hdd sec d hdd',
  Inv fld ->
  hdd_write hdd sec d = Some hdd' ->
  exists fld',fld_write fld sec d = Some fld' /\ Inv fld'.
Proof.
Admitted.

Lemma fld_run_deterministic:
  forall fld cmd fld1 fld2 bh1 bh2,
  fld_run fld cmd fld1 bh1 ->
  fld_run fld cmd fld2 bh2 ->
  fld1 = fld2 /\ bh1 = bh2.
Proof.
Admitted.

Lemma Inv_fld_init: forall f,fld_init = Some f -> Inv f.
Proof.
intros.
(* unfold fld_init in H. *)
(* simpl in H. *)
(* inversion H. *)
(* subst. *)
(* unfold nand_init. *)
unfold Inv.
unfold Inv.Inv.
simpl.
inversion H.
subst.
remember ({|
        bi_state := bs_data;
        bi_used_pages := 0;
        bi_erase_count := 0;
        bi_page_state := pst_set_all ps_erased |}
        :: {|
           bi_state := bs_trans;
           bi_used_pages := 0;
           bi_erase_count := 0;
           bi_page_state := pst_set_all ps_erased |}
           :: blank_bi
           :: blank_bi
                 :: blank_bi
                    :: blank_bi
                       :: blank_bi
                          :: blank_bi
                             :: blank_bi
                                :: blank_bi
                                   :: blank_bi
                                      :: blank_bi
                                         :: blank_bi
                                            :: blank_bi
                                               :: blank_bi :: blank_bi :: nil) as bit_init.
   remember (2
          :: 3
             :: 4
                :: 5
                   :: 6
                      :: 7
                         :: 8 :: 9 :: 10 :: 11 :: 12 :: 13 :: 14 :: 15 :: nil) as fbq_init.
split.
-
  unfold F_Inv.
  split.
  +
    unfold I_pbn_bit_valid.
    simpl.
    intros.
    split.
    (* first *)
    intros.
    assert(Hbit:forall bit,valid_block_no pbn -> exists bi, bit_get bit pbn = Some bi).
      skip.       
    apply (Hbit bit_init H0).
    intros.
    destruct H0 as [bi Hbit].
    assert(HX:bit_get bit_init pbn = Some bi -> valid_block_no pbn).
        skip.
    apply (HX Hbit).
    +
    split.
    {
    unfold I_length_cmt_const.
    simpl.
    auto.
    }
    split.
    {
      simpl.
      unfold I_cmt_pbn_valid.
      intros.
      (* TO DO modify *)
      skip.
    }
    split.
    {
      simpl.
      unfold I_cmt_pbn_not_fbq.
      intros.
      simpl in H0.
      unfold cmt_init in H0.
      simpl in H0.
      assert(HX: cmt_get blank_cmt loc = None).
        skip.
      rewrite H0 in HX.
      inversion HX.
    }
    split.
    {
      simpl.
      unfold I_length_gtd_const.
      simpl.
      unfold GTD_LENGTH.
      auto.
    }
    split.
    {
      simpl.
      unfold I_gtd_pbn_valid.
      intros.
      unfold gtd_init_empty in H0.
      simpl in H0.
      assert(HX: gtd_get blank_gtd loc = None).
        skip.
      rewrite H0 in HX.
      inversion HX.
    }
    split.
    {
      simpl.
      unfold I_gtd_pbn_not_fbq.
      intros.
      unfold gtd_init_empty in H0.
      assert(HX: gtd_get blank_gtd loc = None).
        skip.
      rewrite H0 in HX.
      inversion HX.
    }
    split.
    {
      simpl.
      unfold I_pbn_fbq_valid.
      intros.
      assert(fbq_in fbq_init pbn = true ->valid_block_no pbn).
         skip.
      apply (H1 H0).
    }
    split.
    {
      simpl.
      unfold I_pbn_fbq_state.
      intros.
      right.
      rewrite Heqfbq_init in *.
      unfold fbq_in in *.
      unfold list_inb in *.
      destruct pbn.
      simpl in *.
      congruence.
      destruct pbn.
      simpl in *.
      congruence.
      destruct pbn.
      simpl in *.
      unfold bit_get in H1;
          rewrite Heqbit_init in H1;
          simpl in H1;
          inversion H1;
          simpl; auto.
     destruct pbn.
      simpl in *.
      unfold bit_get in H1;
          rewrite Heqbit_init in H1;
          simpl in H1;
          inversion H1;
          simpl; auto.
      simpl in *.
    destruct pbn.
      simpl in *.
      unfold bit_get in H1;
          rewrite Heqbit_init in H1;
          simpl in H1;
          inversion H1;
          simpl; auto.
      simpl in *.
 
      do 11 (destruct pbn;[(simpl in *;
          unfold bit_get in H1;
          rewrite Heqbit_init in H1;
          simpl in H1;
          inversion H1;
          simpl;
          auto) | idtac]).
      simpl in *.
      congruence.
      (* destruct pbn.  *)
      (* simpl in *. *)
      (* inversion H0. *)
      (* assert (beq_nat pbn 2 = true -> pbn = 2) . admit. *)
      (* destruct (beq_nat pbn 2). *)
      
      (* destruct pbn. *)
      (* unfold fbq_in in H0. *)
      (* simpl in H0. *)
      (* rewrite Heqfbq_init in H0. *)
      (* simpl in H0. *)
      (* inversion H0. *)
      (* destruct pbn. *)
      (* unfold fbq_in in H0. *)
      (* simpl in H0. *)
      (* rewrite Heqfbq_init in H0. *)
      (* simpl in H0. *)
      (* inversion H0. *)

      (* do 14 (destruct pbn;[( *)
      (*     unfold bit_get in H1; *)
      (*     rewrite Heqbit_init in H1; *)
      (*     simpl in H1; *)
      (*     inversion H1; *)
      (*     simpl; *)
      (*     auto) | idtac]). *)
      (* induction pbn. *)
      (* unfold bit_get in H1. *)
      (* rewrite Heqbit_init in H1. *)
      (* simpl in H1. *)
      (* inversion H1. *)
      (* apply IHpbn. *)
      (* assumption. *)
      (* auto. *)
      }
    split.
    {
      unfold I_pbn_fbq_distinguishable.
      simpl.
      intros.
      intros Contra.
      rewrite Contra in H1.
      rewrite <- H1 in H2.
      simpl in H2.
      unfold fbq_get in H2.
      rewrite Heqfbq_init in H2.
      skip.
    }
    {
      unfold I_pbn_trans_record_valid.
      intros.
      (* TO DO remove *)
      skip.
    }
-
  unfold R_Inv.
  unfold J_bi_block_coherent.
  simpl.
  intros.
  unfold FtlProp.chip_bi_coherent.
  unfold nand_init in *.
  unfold chip_get_block in *.
  exists (init_block).
  split.
  skip.
Admitted.
  (* destruct pbn. *)
  (* { *)
    
Admitted.
  (* destruct pbn. *)
 (*  { *)
 (*    simpl in H0. *)
 (*    rewrite Heqbit_init in H0. *)
 (*    simpl in H0. *)
 (*    unfold bit_get in H0. *)
 (*    simpl in H0. *)
 (*    unfold nand_init in *. *)
 (*    skip. *)
 (*  } *)

 (* Admitted. *)

(**  simlation *)
Lemma simu_one_step_progress:
  forall cmd hdd hdd' bh fld,
    Inv fld ->
    R hdd fld ->
    hdd_run hdd cmd hdd' bh->
    exists fld', fld_run fld cmd fld' bh.
Proof.
Admitted.


Lemma simu_one_step_preservation:
  forall cmd hdd hdd' bh fld fld',
    Inv fld ->
    R hdd fld ->
    hdd_run hdd cmd hdd' bh->
    fld_run fld cmd fld' bh->
    Inv fld' /\ R hdd' fld'.
Proof.
Admitted.

(**  simlation more steps *)
Lemma simu_mult_steps_progress:
  forall cmdlist hdd hdd' bh fld,
    Inv fld ->
    R hdd fld ->
    hdd_run_cmd_list hdd cmdlist hdd' bh->
    exists fld', fld_run_cmd_list fld cmdlist fld' bh.
Proof.
Admitted.

`
Lemma simu_mult_steps_preservation:
  forall cmd hdd hdd' bh fld fld',
    Inv fld ->
    R hdd fld ->
    hdd_run_cmd_list hdd cmd hdd' bh->
    fld_run_cmd_list fld cmd fld' bh->
    Inv fld' /\ R hdd' fld'.
Proof.
Admitted.

Theorem Correctness:
  forall  hdd' fld  cmdlist b,
    hdd_run_cmd_list hdd_init cmdlist hdd' b-> fld_init = Some fld ->
    exists fld' ,fld_run_cmd_list fld cmdlist fld' b.
Proof.
Admitted.