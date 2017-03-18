

(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(*   Author: Yu Guo <aciclo@gmail.com>                                        *)
(*                                        Computer Science Department, USTC   *)
(*                                                                            *)
(*           Yishuai Li                                                       *)
(*                                                                            *)
(*                                                                            *)
(* ************************************************************************** *)

(* ************* ************************************* *****)

Require Import LibEx.
Require Import List.
Require Import ListEx.
Require Import Monad.
Require Import Data.

Require Import Params.
Require Import Nand.
Require Import FtlFast2.

Import NewNand.
Import NandData.
Import NandConf.

Lemma rwq_in_rwq_get: 
  forall rwq pbn,

    rwq_in rwq pbn = true 
    -> exists i, rwq_get rwq i = Some pbn.
Proof. 
induction rwq.
unfold rwq_in, rwq_get.
simpl.
intros; discriminate.

unfold rwq_in, rwq_get.
simpl.
intros.
destruct (beq_nat pbn a) eqn:Ha.
exists 0.
rewbnat Ha.
trivial.
assert (pbn <> a).
  intro HF.
  subst a.
  simplbnat.
destruct (IHrwq pbn H) as [i IH].
exists (S i).
trivial.
Qed.

Lemma bit_update_spec : 
  forall bit pbn bi bi',
    bit_get bit pbn = Some bi
    -> exists bit',bit_update bit pbn bi' = Some bit'
                  /\ bit_get bit' pbn = Some bi'
                  /\ (forall pbn', pbn <> pbn'
                                   -> bit_get bit' pbn' = bit_get bit pbn').
Proof.
  unfold bit_update, bit_get.
  intros.
  destruct (list_get_list_set bi' H) as [bit' Hbit'].
  exists bit'.
  split; trivial.
  rewrite (list_get_list_set_eq Hbit').
  split; trivial.
  intros.
  rewrite (list_get_list_set_neq Hbit' H0).
  trivial.
Qed.

Lemma bit_get_update_neq : 
  forall bit pbn bit' bi' pbn',
    bit_update bit pbn' bi' = Some bit'
    -> pbn <> pbn'
    -> bit_get bit' pbn = bit_get bit pbn.
Proof.
  unfold bit_update, bit_get.
  intros.
  rewrite (list_get_list_set_neq H (neq_sym H0)).
  trivial.
Qed.
Arguments bit_get_update_neq [bit pbn bit' bi' pbn' _ _ ].

Lemma bit_get_update_eq : 
  forall bit pbn bi bit',
    bit_update bit pbn bi = Some bit'
    -> bit_get bit' pbn = Some bi.
Proof.
  unfold bit_update, bit_get.
  intros.
  rewrite (list_get_list_set_eq H).
  trivial.
Qed.
Arguments bit_get_update_eq [bit pbn bi bit' _].

Lemma bmt_update_spec : 
  forall bmt lbn bmr bmr',
    bmt_get bmt lbn = Some bmr 
    -> exists bmt', bmt_update bmt lbn bmr' = Some bmt'
                    /\ bmt_get bmt' lbn = Some bmr'
                    /\ forall lbn', 
                         lbn' <> lbn 
                         -> bmt_get bmt' lbn' = bmt_get bmt lbn'.
Proof.
  unfold bmt_get, bmt_update.
  intros.
  destruct (list_get_list_set bmr' H) as [bmt' Hbmt'].
  exists bmt'.
  split; trivial.
  rewrite (list_get_list_set_eq Hbmt').
  split; trivial.
  intros.
  rewrite (list_get_list_set_neq Hbmt' (neq_sym H0)).
  trivial.
Qed.

Lemma bmt_get_update_eq : 
  forall bmt lbn bmr bmt',
    bmt_update bmt lbn bmr = Some bmt'
    -> bmt_get bmt' lbn = Some bmr.
Proof.
  unfold bmt_update, bmt_get.
  intros.
  rewrite (list_get_list_set_eq H).
  trivial.
Qed.
Arguments bmt_get_update_eq [bmt lbn bmr bmt' _].

Lemma bmt_get_update_neq : 
  forall bmt lbn bmt' bmr' lbn',
    bmt_update bmt lbn' bmr' = Some bmt'
    -> lbn <> lbn'
    -> bmt_get bmt' lbn = bmt_get bmt lbn.
Proof.
  unfold bmt_update, bmt_get.
  intros.
  rewrite (list_get_list_set_neq H (neq_sym H0)).
  trivial.
Qed.
Arguments bmt_get_update_neq [bmt lbn bmt' bmr' lbn' _ _ ].

Lemma swb_len_less_than_constant :
  forall swb ,
    swb_len swb <= 1.
Proof.
  unfold swb_len.
  destruct swb.
  omega.
  omega.
Qed.

Lemma rwq_in_elim : forall rwq rwb,
                      rwq_in rwq rwb = true
                      -> exists i, rwq_get rwq i = Some rwb.
Proof.
intros rwq rwb Hri.
apply (rwq_in_rwq_get rwq rwb Hri).
Qed.


(*  -------------------------------------------------------------

  Lemmas for free_block_queue 

*)

(* Old name: Lemma pbn_not_in_fbq_presev_fbq_enq :  *)
Lemma fbq_not_in_presev_fbq_enq : 
  forall fbq pbn fbq' pbn',
    fbq_in fbq pbn = false
    -> fbq_enq fbq pbn' = Some fbq'
    -> pbn <> pbn' 
    -> fbq_in fbq' pbn = false.
Proof.
  induction fbq.
    unfold fbq_in, fbq_enq.
    intros pbn fbq' pbn' Hin Henq Hneq.
    injection Henq.
    intro H.
    subst fbq'.
    simpl.
    simplbnat.
    trivial.

  unfold fbq_in.
  simpl.
  intros pbn fbq' pbn' Hin Henq Hneq.
  destruct fbq'.
    unfold fbq_enq in Henq.
    simpl in Henq.
    discriminate.
  inversion Henq.
  subst b.
  simpl.
  destruct (beq_nat pbn a) eqn:Hb.
    trivial.
  eapply IHfbq; eauto.
  unfold fbq_enq.
  trivial.
Qed.

(* Old name: Lemma fbq_in_fbq_enq_fbq_in :  *)
Lemma fbq_in_preserv_fbq_enq : 
  forall pbn fbq pbn' fbq',
    pbn <> pbn'
    -> fbq_enq fbq pbn' = Some fbq' 
    -> fbq_in fbq' pbn = fbq_in fbq pbn.
Proof.
  induction fbq.
    intros.
    unfold fbq_enq, fbq_in in * .
    simpl in H0.
    inversion H0.
    subst fbq'.
    simpl.
    simplbnat.
    trivial.
  destruct fbq'.
    intros.
    unfold fbq_enq in H0.
    discriminate.
  intros.
  unfold fbq_enq in * .
  simpl in * .
  inversion H0.
  subst b fbq'.
  simpl.
  unfold fbq_in in * .
  simpl.
  clear H0.
  destruct (beq_nat pbn a) eqn:Hb.
    trivial.
  eapply IHfbq; eauto.
Qed.

Lemma fbq_enq_fbq_in : 
  forall pbn fbq fbq',
    fbq_enq fbq pbn = Some fbq' 
    -> fbq_in fbq' pbn = true.
Proof.
  unfold fbq_enq, fbq_in.
  induction fbq.
    intros.
    injection H.
    intro; subst fbq'.
    simpl.
    simplbnat.
    trivial.
  intros.
  injection H.
  intro; subst fbq'.
  simpl.
  destruct (beq_nat pbn a) eqn:Hb.
    trivial.
  eapply IHfbq.
  trivial.
Qed.

Lemma fbq_enq_fbq_len_addone : 
  forall fbq pbn fbq',
    fbq_enq fbq pbn = Some fbq'
    -> fbq_len fbq' = 1 + fbq_len fbq.
Proof.
  induction fbq.
    intros.
    unfold fbq_enq in H.
    injection H.
    intro; subst fbq'.
    simpl.
    trivial.
  intros.
  unfold fbq_enq in H.
  injection H.
  intro; subst fbq'.
  simpl.
  rewrite (IHfbq pbn (list_append fbq pbn)); eauto.
Qed.

Lemma fbq_deq_fbq_length_subone : 
  forall fbq pbn fbq',
    fbq_deq fbq = Some (pbn, fbq')
    -> fbq_len fbq = S (fbq_len fbq').
Proof.
  unfold fbq_deq.
  induction fbq; simpl; intros; auto.
    discriminate.
  injection H; intros; subst a fbq'.
  trivial.
Qed.

Lemma fbq_not_in_preserv_fbq_deq : 
  forall fbq pbn fbq' pbn',
    fbq_in fbq pbn = false 
    -> fbq_deq fbq = Some (pbn', fbq')
    -> fbq_in fbq' pbn = false.
Proof.
  induction fbq; unfold fbq_in, fbq_deq; simpl; intros; auto.
    discriminate.
  injection H0; intros; subst a fbq'.
  destruct (beq_nat pbn pbn') eqn:Hpbn; trivial.
  discriminate.
Qed.

Lemma fbq_not_in_preserv_fbq_enq : 
  forall fbq pbn fbq' pbn',
    pbn <> pbn' 
    -> fbq_in fbq pbn = false
    -> fbq_enq fbq pbn' = Some fbq'
    -> fbq_in fbq' pbn = false.
Proof.
  unfold fbq_in, fbq_enq.
  induction fbq; simpl; intros; auto.
    injection H1; intros; subst fbq'.
    simpl.
    simplbnat.
    trivial.
  injection H1; intros; subst fbq'.
  simpl.
  destruct (beq_nat pbn a) eqn: Ha.
    discriminate.
  eauto.
Qed.

Lemma fbq_in_fbq_get: 
  forall fbq pbn,
    fbq_in fbq pbn = true 
    -> exists i, fbq_get fbq i = Some pbn.
Proof.
  induction fbq.
    unfold fbq_in, fbq_get. 
    simpl.
    intros; discriminate.
  unfold fbq_in, fbq_get.
  simpl.
  intros.
  destruct (beq_nat pbn a) eqn:Ha.
    exists 0.
    rewbnat Ha.
    trivial.
  assert (pbn <> a).
    intro HF.
    subst a.
    simplbnat.
  destruct (IHfbq pbn H) as [i IH].
  exists (S i).
  trivial.
Qed.

Lemma fbq_get_fbq_deq_fbq_get: 
  forall fbq i pbn pbn' fbq',
    fbq_get fbq (S i) = Some pbn
    -> fbq_deq fbq = Some (pbn', fbq')
    -> fbq_get fbq' i = Some pbn.
Proof.
  induction fbq.
    intros.
    unfold fbq_get, fbq_deq in * .
    discriminate.
  intros.
  unfold fbq_get in H.
  unfold fbq_deq in H0.
  injection H0.
  intros; subst fbq' a.
  simpl in H.
  trivial.
Qed.

Lemma fbq_get_fbq_rdeq_fbq_get: 
  forall fbq i pbn pbn' fbq',
    fbq_get fbq i = Some pbn
    -> fbq_deq fbq' = Some (pbn', fbq)
    -> fbq_get fbq' (S i) = Some pbn.
Proof.
  induction fbq.
    intros.
    unfold fbq_get in H .
    unfold list_get in H.
    destruct i; discriminate.
  intros.
  unfold fbq_get in H.
  destruct fbq'.
    simpl in H0.
    discriminate.
  simpl in H0.
  injection H0.
  intros; subst fbq' b.
  unfold fbq_get.
  simpl.
  apply H.
Qed.

Lemma fbq_deq_fbq_get : 
  forall fbq pbn fbq',
    fbq_deq fbq = Some (pbn, fbq')
    -> fbq_get fbq 0 = Some pbn.
Proof.
  induction fbq.
    intros.
    simpl in * .
    discriminate.
  intros pbn fbq' H.
  unfold fbq_deq in H.
  injection H.
  intros; subst fbq' a.
  unfold fbq_get.
  simpl.
  trivial.
Qed.

Lemma fbq_deq_fbq_in : 
  forall fbq pbn fbq',
    fbq_deq fbq = Some (pbn, fbq') 
    -> fbq_in fbq pbn = true.
Proof.
  unfold fbq_deq, fbq_in.
  induction fbq; simpl; intros; auto.
    discriminate.
  injection H; intros; subst a fbq'.
  simplbnat.
  trivial.
Qed.
  
Lemma fbq_in_preserv_fbq_deq : 
  forall fbq pbn fbq' pbn',
    fbq_in fbq pbn = true
    -> pbn' <> pbn
    -> fbq_deq fbq = Some (pbn', fbq')
    -> fbq_in fbq' pbn = true.
Proof.
  unfold fbq_in, fbq_deq.
  induction fbq; simpl; intros; auto.
    discriminate.
  injection H1; intros; subst a fbq'.
  simplbnat.
  trivial.
Qed.

Lemma fbq_enq_spec : 
  forall fbq pbn,
    exists fbq', fbq_enq fbq pbn = Some fbq'.
Proof.
  intros.
  unfold fbq_enq.
  exists (list_append fbq pbn).
  trivial.
Qed.

Lemma fbq_get_fbq_enq_fbq_get_rev: 
  forall fbq fbq' i pbn pbn',
    fbq_enq fbq pbn' = Some fbq'
    -> fbq_get fbq' i = Some pbn
    -> pbn = pbn' /\ i = fbq_len fbq \/ fbq_get fbq i = Some pbn .
Proof.
  induction fbq; simpl; intros; trivial.
    unfold fbq_enq in H.
    injection H; intro; subst fbq'; clear H.
    unfold fbq_get in H0.
    simpl in H0.
    destruct i.
      injection H0; intro; subst pbn'; trivial.
      left; split; trivial.
    destruct i; discriminate.
  destruct i.
    unfold fbq_enq in H.
    injection H; intro; subst fbq'; auto.
  destruct fbq'.
    unfold fbq_enq in H.
    discriminate H.
  assert (fbq_enq fbq pbn' = Some fbq').
    clear - H.
    unfold fbq_enq in * .
    simpl in H.
    injection H; intros; subst.
    trivial.
  assert (fbq_get fbq' i = Some pbn).
    clear - H0.
    unfold fbq_get in * .
    simpl in H0.
    trivial.
  destruct (IHfbq fbq' i pbn pbn' H1 H2).
    destruct H3.
    left; subst; split; trivial.
  right.
  clear - H3.
  unfold fbq_get in * .
  simpl.
  trivial.
Qed.

Lemma fbq_not_in_fbq_get_some_implies_false: 
  forall fbq pbn,
    fbq_in fbq pbn = false
    -> forall i, fbq_get fbq i = Some pbn 
                 -> False.
Proof.
  unfold fbq_get.
  induction fbq; simpl; intros; auto.
    destruct i; discriminate.
  assert (fbq_in fbq pbn = false).
    unfold fbq_in in * .
    simpl in * .
    destruct (beq_nat pbn a).
      discriminate.
    trivial.
  destruct i.
    injection H0; intro; subst a; auto.
    unfold fbq_in in H.
    simpl in H.
    simplbnat.
  apply IHfbq with pbn i ; auto.
Qed.

Lemma fbq_get_fbq_deq_fbq_get_rev: 
  forall fbq i pbn pbn' fbq',
    fbq_deq fbq = Some (pbn', fbq')
    -> fbq_get fbq' i = Some pbn
    -> fbq_get fbq (S i) = Some pbn.
Proof.
  induction fbq.
    intros.
    unfold fbq_get, fbq_deq in * .
    discriminate.
  intros.
  destruct i.
    simpl in *.
    unfold fbq_get.
    simpl.
    injection H; intros; subst fbq'; trivial. 
  unfold fbq_deq in H.
  injection H; intros; subst a fbq'; auto.
Qed.

Lemma rwq_notin_cons_elim : 
  forall rwb rwq pbn,
    rwq_in (cons rwb rwq) pbn = false 
    -> beq_nat rwb pbn = false /\ rwq_in rwq pbn = false.
Proof.
intros rwb rwq pbn Hri.
split.

destruct (beq_nat rwb pbn) eqn:HF;trivial.                              
SearchAbout beq_nat.
apply beq_true_eq in HF.
rewrite HF in Hri.
unfold rwq_in in Hri.
simpl in Hri.
assert(HX: beq_nat pbn pbn = true).
  apply beq_refl.
rewrite->HX in Hri.
apply Hri.

destruct (rwq_in rwq pbn) eqn:HF;trivial.
unfold rwq_in in *.
simpl in Hri.
rewrite HF in Hri.
destruct (beq_nat pbn rwb);
apply Hri.
Qed.

Lemma rwq_in_cons_intro : 
  forall rwb rwq pbn,
    beq_nat rwb pbn = true \/ rwq_in rwq pbn = true
    -> rwq_in (cons rwb rwq) pbn = true.
Proof.
intros rwb rwq pbn Hx.
destruct Hx as [Heq | ].                            
apply beq_true_eq in Heq.
rewrite Heq.
unfold rwq_in.
simpl.
assert(H1: beq_nat pbn pbn = true).
  apply beq_refl.
rewrite H1.
reflexivity.

unfold rwq_in.
simpl.
destruct (beq_nat pbn rwb);trivial.
Qed.


(* ********************************** pmt lemmas **************** *)

Lemma pmt_len_preserv_pmt_invalidate_lbn:
  forall pmt lbn,
    pmt_len (pmt_invalidate_lbn pmt lbn) = pmt_len pmt.
Proof.
  induction pmt.
  intros.
  unfold pmt_len.
  unfold pmt_invalidate_lbn.
  trivial.

  intros.
  simpl.
  destruct a.
  simpl.
  rewrite IHpmt.
  trivial.
  destruct (beq_nat lbn lbn0) eqn:Heq.
    simpl.
    rewrite IHpmt; trivial.
  simpl; rewrite IHpmt; trivial.
  simpl.
  rewrite IHpmt; trivial.
Qed.

Lemma pmt_invalidate_lbn_elim:
  forall pmt lbn pmt',
    pmt' = pmt_invalidate_lbn pmt lbn
    -> forall loc, 
         (pmt_get pmt loc = None
         -> pmt_get pmt' loc = None)
         /\ (pmt_get pmt loc = Some (pmte_empty)
          -> pmt_get pmt' loc = Some (pmte_empty))
         /\ (pmt_get pmt loc = Some (pmte_invalid)
             -> pmt_get pmt' loc = Some (pmte_invalid))
         /\ (forall lbn' off', 
               pmt_get pmt loc = Some (pmte_log lbn' off')
               -> beq_nat lbn lbn' = true
               -> pmt_get pmt' loc = Some (pmte_invalid))
         /\ (forall lbn' off', 
               pmt_get pmt loc = Some (pmte_log lbn' off')
               -> beq_nat lbn lbn' = false
               -> pmt_get pmt' loc = Some (pmte_log lbn' off')).
Proof.
  induction pmt.
  simpl.
  intros.
  subst pmt'.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  intros.
  substbnat.
  unfold pmt_get in H.
  simpl in H.
  destruct loc; discriminate.
  
  intros.
  simpl in H.
  destruct pmt'.
    destruct a; try discriminate.
    destruct (beq_nat lbn lbn0); try discriminate.
  destruct loc.
    unfold pmt_get.
    simpl.
    destruct a; inversion H; subst.
    split.
      intro; discriminate.
    split; trivial.
    split; trivial.
    split; trivial.
    split.
      intro; discriminate.
    split.
      intro; discriminate.
    split.
      intro; discriminate.
    split.
      intros.
      inversion H0.
      subst off' lbn0.
      rewrite H2 in H.
      inversion H.
      trivial.
    intros.
    inversion H0.
    subst lbn0 off'.
    rewrite H2 in H.
    inversion H; trivial.
    split.
      intro; discriminate.
    split; trivial.
    split; trivial.
    split.
      intros; discriminate.
    intros; discriminate.
  destruct (IHpmt lbn (pmt_invalidate_lbn pmt lbn) (refl_equal _) loc) as [IH1 [IH2 [IH3 IH4] ] ].
  unfold pmt_get.
  simpl.
  unfold pmt_get in *.
  destruct a.
  inversion H.
  subst p pmt'.
  split; trivial.
  split; trivial.
  split; trivial.
  destruct (beq_nat lbn lbn0) eqn:Hlbn.
  inversion H.
  subst p pmt'.
  split; trivial.
  split; trivial.
  split; trivial.
  inversion H.
  subst p pmt'.
  split; trivial.
  split; trivial.
  split; trivial.
  inversion H.
  subst p pmt'.
  split; trivial.
  split; trivial.
  split; trivial.
Qed.

