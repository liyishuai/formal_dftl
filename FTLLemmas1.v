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

Definition valid_logic_block_no (lbn:block_no) :Prop := bvalid_logical_block_no lbn = true.

Lemma find_cmt_init_spec:forall lpn ,valid_logic_page_no lpn -> find_cmtrecord cmt_init lpn 0 = None.
Proof.
intros.
unfold find_cmtrecord.
simpl.
reflexivity.
Qed.

(* Lemma test:forall a b x, x < a * b -> NPeano.div x a < b. *)
(* Proof. *)
(* intros. *)
(* remember (a *b) as HX. *)
(* generalize dependent a. *)
(* generalize dependent b. *)
(* induction a. *)
(* skip. *)
(* intros. *)
(* simpl. *)
(* unfold NPeano.div. *)
(* Admitted. *)

(* Lemma find_gtd_init_spec1:forall lpn ,valid_logic_page_no lpn ->  *)
(*                                      exists n,gtd_look_by_lpn gtd_init_empty lpn = Some n. *)
(* Proof. *)
(* intros. *)
(* unfold gtd_look_by_lpn. *)
(* unfold valid_logic_page_no in H. *)
(* assert(HX:Dftl2.bvalid_logical_page_no lpn = true). *)
(*   apply H. *)
(* rewrite HX. *)
(* exists (NPeano.div lpn RECORD_PER_TRANS). *)
(* split. *)
(* Qed. *)

(* Lemma find_gtd_init_spec2:forall lpn ,valid_logic_page_no lpn ->  *)
(*                                      (forall n,gtd_look_by_lpn gtd_init_empty lpn = Some n -> *)
(*                                        n < 16). *)
(* Proof. *)
(* intros. *)
(* unfold gtd_look_by_lpn. *)
(* unfold valid_logic_page_no in H. *)
(* assert(HX:Dftl2.bvalid_logical_page_no lpn = true). *)
(*   apply H. *)
(* rewrite HX. *)
(* exists (NPeano.div lpn RECORD_PER_TRANS). *)
(* split. *)
(* reflexivity. *)
(* assert(HX2:lpn < 8 * 16). *)
(*   unfold bvalid_logical_page_no in H. *)
(*   simpl in H. *)
(*   apply blt_true_lt. *)
(*   apply H. *)
(* assert(HX3:RECORD_PER_TRANS =8). *)
(* skip. *)
(* rewrite HX3. *)
(* simpl. *)
(* Admitted. *)

Lemma find_gtd_init_spec2:forall lpn,valid_logic_page_no lpn -> 
                                     (forall n, gtd_look_by_lpn gtd_init_empty lpn = Some n ->
                                     n < 16).
Proof.
Admitted.

(* Lemma gtd_init_spec: forall lpn num ,valid_logical_page_no lpn ->  *)
(*                                      gtd_look_by_lpn gtd_init_empty lpn ->  *)
(*                                      lpn >= (num * 8). *)
(* Proof. *)
(* Admitted. *)

Lemma valid_logic_page_no_iff:forall lpn, valid_logic_page_no lpn <-> Dftl2.bvalid_logical_page_no lpn = true.
Proof.
split;
intros;unfold valid_logic_page_no in H;
apply H.
Qed.

Lemma Ftl_read_init_spec: forall lpn  ftl,fld_init = Some (nand_init, ftl) -> 
                          valid_logic_page_no lpn ->
                          exists c,FTL_read nand_init ftl lpn = Some (zero_page,c:(Nand.chip * FTL)).
Proof.
intros.
unfold FTL_read.
assert(HX0:Dftl2.bvalid_logical_page_no lpn = true).
  unfold valid_logic_page_no in H0.
  apply H0.
rewrite HX0.
assert(HX:fld_init = Some (nand_init,ftl) -> ftl_cmt_table ftl = cmt_init).
   intros.
   inversion H1.
   unfold cmt_init.
   simpl.
   reflexivity.
assert(HS:ftl_cmt_table ftl = cmt_init).
  apply HX.
  apply H.
rewrite HS.
rewrite (find_cmt_init_spec lpn H0).
assert(HX1:fld_init = Some (nand_init,ftl) -> ftl_gtd_table ftl = gtd_init_empty).
  intros.
  inversion H1.
  simpl.
  reflexivity.
assert(HS1:ftl_gtd_table ftl = gtd_init_empty).
  apply HX1.
  apply H.
rewrite HS1.
assert(HS2:exists num,gtd_look_by_lpn gtd_init_empty lpn = Some num).
  skip.
destruct HS2 as [num HS2'].
rewrite HS2'.
unfold gtd_init_empty.
unfold blank_gtd.
unfold gtd_get.
rewrite list_get_list_repeat_list.
exists (nand_init ,ftl).
reflexivity.
assert (HS3:num < 16).
  apply (find_gtd_init_spec2 lpn H0  num HS2').
unfold GTD_LENGTH.
skip.
Qed.


