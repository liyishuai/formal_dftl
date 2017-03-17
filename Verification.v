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
Admitted.

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