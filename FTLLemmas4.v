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
Require Import FTLLemmas5.

Definition FTL_read_data (c:chip) (f:FTL) (lpn:page_no) :option data :=
  match FTL_read c f lpn with
      | Some (d,_) => Some d
      | None => None
  end.


Lemma ftl_write_spec_1 : forall (c : chip) (f : FTL) (lpn:page_no) (d : data),
       Inv c f ->
       valid_logic_page_no lpn ->
       exists (c' : chip) (f' : FTL),
         FTL_write c f lpn d = Some (c', f').
Proof.
Admitted.

Lemma ftl_write_spec_2 : forall (c : chip) (f : FTL) (lpn:page_no) (d : data),
       Inv c f ->
       valid_logic_page_no lpn ->
       exists (c' : chip) (f' : FTL),
         FTL_write c f lpn d = Some (c', f') /\
         (exists c''  f'',FTL_read c' f' lpn = Some (d,(c'',f''))).
Proof.
Admitted.

Lemma ftl_write_spec : forall (c : chip) (f : FTL) (lpn:page_no) (d : data),
       Inv c f ->
       valid_logic_page_no lpn ->
       exists (c' : chip) (f' : FTL),
         FTL_write c f lpn d = Some (c', f') /\
         Inv c' f' /\
         (exists c''  f'',FTL_read c' f' lpn = Some (d,(c'',f''))) /\
         (forall lpn' : page_no,
          lpn <> lpn' -> FTL_read_data c' f' lpn' = FTL_read_data c f lpn').
Proof.
intros c f lpn d Hv HLPN.
unfold Inv in Hv.
destruct Hv as [Hvf Hvr].
unfold F_Inv in Hvf.
destruct Hvf as [HI1 [HI2 [HI3 [HI4 [HI5 [HI6 [HI7 [HI8 [HI9 [HI10 HI11]]]]]]]]]].
unfold R_Inv in Hvr.
(* start to prove *)
unfold FTL_write.
assert(HGLBN: exists lbn off ,get_lbnandoff_by_lpn lpn BLOCKS = Some (lbn,off)).
  skip.
destruct HGLBN as [lbn [off HGLBN']].
rewrite HGLBN'.
remember f as Hf.
destruct f as [bit fbq cmt gtd cur_dblock cur_tblock].
simpl in *.
simpl.
clear HGLBN'.
assert (HVLBN: valid_block_no cur_dblock).
  skip.
destruct (HI1 cur_dblock) as [HBI1 HBI2].
destruct (HBI1 HVLBN) as [curbi HBGET].
rewrite HeqHf.
simpl.
rewrite HeqHf in *.
simpl in *.
rewrite HBGET.
(* Print FTL. *)

(* assert (Hcurbi':exists bi, bit_get bit cur_dblock = Some bi). *)
(*   skip. *)
(* destruct Hcurbi' as [curbi Hcurbi]. *)
destruct (check_block_is_full curbi) eqn:HFUL.
-
  skip.
-
  Print block_info.
  assert (HWP:lpn_to_lbn_off lpn = (lbn,off)). 
    skip.
  assert (HX1: cur_dblock = current_data_block Hf).
    skip.
  assert (HX2: exists poff , poff = bi_used_pages curbi).
    skip.
  destruct HX2 as [poff Hpoff].
  rewrite <- Hpoff.
  destruct (write_data_block_noemp c Hf bit cur_dblock curbi poff lpn lbn off d 
                                   HX1 HBGET HFUL Hpoff HLPN HWP) as
        [c' [bi' [HW1 [HW2 [HW3 HW4]]]]].
  exists c'.
  replace  (write_data_block c curbi cur_dblock poff d (Some (lbn, off))
       (ps_data lpn)
  ) with (Some (c',bi')).
  simpl.
  assert (Hbit: exists bit' ,bit_update bit cur_dblock bi' = Some bit').
    skip.
  destruct Hbit as [bit' Hbit''].
  rewrite Hbit''.
  rewrite <- HeqHf.              
  unfold cmt_update_when_ftl_write.
  simpl.
  assert(Hcurd:valid_block_no cur_dblock).
     skip.
  destruct (bit_update_spec bit' cur_dblock Hcurd) as [bi3 Hbit3].
  rewrite Hbit3.
  (** It have 7 different cases **)
  
  (** 1 cases **)
  destruct (find_cmtrecord cmt (lbn * PAGES_PER_BLOCK + off) 0) eqn:Hcmt.
  assert(Hcmt_get:exists record,cmt_get cmt n = Some record).
    skip.
  destruct Hcmt_get as [record cmt_get_rerd].
  rewrite cmt_get_rerd.
  assert(Hcmt_trans:exists pbn off f, cmt_get_trans record = Some (pbn,off,f)).
    skip.
  destruct Hcmt_trans as [record_pbn [record_off [record_flag Htrans]]].
  rewrite Htrans.
  destruct (find_empty_cmt cmt 0) eqn:Hempty_cmt.
    + (* The cmt have the empty place *)
      destruct (record_flag) eqn:Hflag.
      destruct (invalid_old_page_spec bit' record_pbn record_off) as [bit4 Hinvalid].
      rewrite Hinvalid.
      exists {|
       ftl_bi_table := bit4;
       ftl_free_blocks := fbq;
       ftl_cmt_table := insert_cmt
                          (remove_cmt cmt (lbn * PAGES_PER_BLOCK + off))
                          (cmt_trans (lbn * PAGES_PER_BLOCK + off) cur_dblock
                             (pred (bi_used_pages bi3)) dirty) 
                          (pred n0);
       ftl_gtd_table := gtd;
       current_data_block := cur_dblock;
       current_trans_block := cur_tblock |}.
      split.
      auto.
      split.
      skip.
      (* (* Prove Inv*) *)
      
      (* split. *)
      (*  * *)
      (*    unfold Inv. *)
      (*    unfold F_Inv. *)
      (*    split. *)
      (*    unfold I_pbn_bit_valid. *)
      (*    split. *)
      (*      { *)
      (*        simpl. *)
      (*        split. *)
      (*         {{ *)
      (*             intros. *)
      (*             unfold bit_get. *)
      (*             skip. *)
      (*         }} *)
      (*         {{ *)
      (*             intros. *)
      (*             skip. *)
      (*         }} *)
      (*       } *)
      (*      { *)
      (*        split. *)
      (*        {{ *)
      (*        unfold I_length_cmt_const. *)
      (*        simpl. *)
      (*        unfold list_len. *)
      (*        simpl. *)
      (*        skip. *)
      (*        }} *)
      (*        split. *)
      (*        unfold I_cmt_pbn_valid. *)
      (*        simpl. *)
      (*        skip. *)
      (*        split. *)
      (*        unfold I_cmt_pbn_not_fbq. *)
      (*        simpl. *)
      (*        intros. *)
      
      (* 1.3 Prove read the same *)
      unfold FTL_read.
      assert(Hvalid': Dftl2.bvalid_logical_page_no lpn = true).
        skip.
      rewrite Hvalid'.
      simpl.
      skip.
Admitted.
