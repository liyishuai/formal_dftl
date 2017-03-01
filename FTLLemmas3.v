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

Lemma ftl_read_write_at_same_addr : 
  forall c f lpn d c' f',
    Inv c f 
    -> FTL_write c f lpn d = Some (c', f')
    -> exists c'' f'',FTL_read c' f' lpn = Some (d,(c'',f'') ).
Proof.
  intros c f lpn d c' f' HI HW.
  assert (HVP: valid_logic_page_no lpn).
    (* destruct (ftl_write_some_implies_valid_addr _ _ _ _ _ _ _ HI Hw) as [Hx Hy]. *)
    skip.
  destruct (ftl_write_spec c f lbn lpo v HI Hv Ho) as [c'' [f'' [Hw'' [HI'' [Hr'' _]]]]].
  rewrite Hw in Hw''.
  injection Hw''; intros; subst c'' f''.
  trivial.
Qed.
