Set Warnings "-notation-overridden,-parsing".
Add LoadPath "Purdue\CS456\Volume 2\" as PLF.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
Import ListNotations.
From PLF Require Import Smallstep.
Require Import Maps.
From PLF Require Import Imp.

Lemma normal_form_no_step : forall t t', 
  normal_form step t -> ~t --> t'.
Proof.
  intros t t' nf rtt'.
  unfold normal_form in nf.
  Admitted.

Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
 intros X y1 y2 [p11 p12] [p21 p22].
 generalize dependent y2.
 unfold step_normal_form in *.
  induction p11; intros y2 p21 p22.
  - inversion p21; subst.
    reflexivity.
    assert (H1: ~x --> y).  {
      now apply normal_form_no_step.
    }
    intuition.
  - inversion p21; subst.
    + 
      assert (Hdoub: z = y2). {
        assert (H1: ~ y2 --> y). {
        now apply normal_form_no_step.
      }
      apply IHp11; try trivial.
      assert (H2: y = y2). {
        now apply step_deterministic with y.
      }
      now rewrite H2.
      }
      apply Hdoub.
    + apply IHp11.
      apply p12.
      assert (Hwhy: y=x). {
        admit.
      }
      rewrite Hwhy.
      apply p21.
      apply p22.
Admitted.

Theorem eval__multistep : forall t n,
  t ==> n -> t -->* C n.
Proof.
 intros t n H.
  induction H.
  - constructor.
  - apply multi_trans with (P (C n1) t2).
      apply multistep_congr_1.
      assumption.
    apply multi_trans with (P (C n1) (C n2)).
      apply multistep_congr_2.
      constructor.
      assumption.
    apply multi_step with (C (n1 + n2)).
      apply ST_PlusConstConst.
      apply multi_refl.
Qed.

Lemma step__eval : forall t t' n,
     t --> t' ->
     t' ==> n ->
     t  ==> n.
Proof.
 intros t t' n step_t_t' eval_t'_n.
  generalize dependent t.
  induction eval_t'_n; intros t step_t_t'.
  - inversion step_t_t'.
    apply E_Plus.
    constructor.
    constructor.
  - inversion step_t_t'; subst.
    apply IHeval_t'_n1 in H1.
    now apply E_Plus.
    apply IHeval_t'_n2 in H3.
    now apply E_Plus.
Qed.