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

Lemma ftl_write_spec : forall (c : chip) (f : FTL) (lpn:page_no) (d : data),
       Inv c f ->
       valid_logic_page_no lpn ->
       exists (c' : chip) (f' : FTL),
         FTL_write c f lpn d = Some (c', f') /\
         Inv c' f' /\
         (exists c''  f'',FTL_read c' f' lpn = Some (d,(c'',f''))) /\
         (forall lpn' : page_no,
          lpn <> lpn' -> FTL_read c' f' lpn' = FTL_read c f lpn').
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
  assert (Hbit: exists bi'' ,bit_update bit cur_dblock bi' = Some bi'').
    skip.
  destruct Hbit as [bi'' Hbit''].
  rewrite Hbit''.
  rewrite <- HeqHf.
  