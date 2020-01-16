Set Implicit Arguments.
Require Import Omega.
Require Import PeanoNat.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Check mult (S (O)) (S (O)).

Lemma plus_ident (x:nat) :
  forall x, plus x 0 = x.
Proof.
  intros.
  induction x0.
  - reflexivity.
  - simpl.
    rewrite IHx0.
    reflexivity.
Qed.

Lemma mult_0 (x:nat):
  forall x, mult x 0 = 0.
Proof.
  intros n.
  destruct n.
  - simpl.
  reflexivity.
  - simpl.
    intuition.
Qed.

Lemma mult_ident (x:nat):
  forall x, mult x 1 = x.
Proof.
  intros.
  induction x0.
  - reflexivity.
  - simpl.
    rewrite  IHx0.
    reflexivity.
Qed.
Lemma mult_comm (x:nat) (y:nat):
  forall x y, mult x y = mult y x.
Proof.
  intros x0.
  induction x0; intros n.
  - simpl.
  symmetry.
  apply Nat.mul_0_r.
  - intuition.
Qed.
Lemma mult_S x y :
  mult x (S y) = plus (mult x y) x.
Proof. 
  induction x.
  - (*mult 0 (S y) = plus (mult 0 y) 0*)
    reflexivity.
  - (*mult (S x) (S y) = plus (mult (S x) y) (S x)*)
    intuition.
Qed.

Lemma mult_com (x y : nat) :
  mult x y = mult y x.
Proof.
  induction x.
  - rewrite mult_0.
    reflexivity.
    assumption.
  - rewrite mult_comm.
    reflexivity.
    assumption.
    assumption.
Qed.

Lemma mult_dist (x y z: nat) :
  mult (plus x y) z = plus (mult x z) (mult y z).
Proof.
  induction x.
  - reflexivity.
  - induction y.
    { (*mult (plus (S x) 0) z = plus (mult (S x) z) (mult 0 z)*)
      rewrite plus_ident.
      symmetry.
      rewrite mult_com.
      assert (H: mult 0 z = 0). {
        rewrite mult_com.
        rewrite mult_0.
        reflexivity.
        assumption.
      }
      rewrite H.
      rewrite plus_ident.
      reflexivity.
      assumption.
      assumption.
    }
    { (*mult (plus (S x) (S y)) z = plus (mult (S x) z) (mult (S y) z)*)
    intuition.
    }
Qed.

(*  For this part of the homework, we will consider how we might reason about a
 *  a simple language of arithmetic expressions. *)

  Inductive arith : Set :=
  | Const (n : nat)
  | Plus (e1 e2 : arith)
  | Times (e1 e2 : arith).

  (* Here are a few examples of specific expressions. *)
  Example ex1 := Const 42.
  Example ex2 := Plus (Const 1) (Times (Const 2) (Const 3)).

  (* Write a definition that computes the size of an arithmetic expression
   * This should be equivalent to the size of the expression's abstract syntax tree
   *) 
  Fixpoint size (e : arith) : nat :=
    match e with
    | Const _ => 1
    | Plus e1 e2 => size e1 + size e2
    | Times e1 e2 => size e1 + size e2
    end.

  (* What's the longest path from the root of a syntax tree to a leaf? *)
  Fixpoint depth (e : arith) : nat :=
    match e with
    | Const _ => 1
    | Plus e1 e2 => 1 + max (depth e1) (depth e2)
    | Times e1 e2 => 1 + max (depth e1) (depth e2)
    end.

  Theorem depth_le_size : forall e, depth e <= size e.
  Proof.
    (* you will need to use the omega tactic in this proof. *)
    (* SearchAbout is also your friend! *)
    induction e.
    reflexivity.
    SearchAbout Plus.
  Admitted.

  Fixpoint commuter (e : arith) : arith :=
    match e with
    | Const _ => e
    | Plus e1 e2 => Plus (commuter e2) (commuter e1)
    | Times e1 e2 => Times (commuter e2) (commuter e1)
    end.

  Theorem size_commuter : forall e, size (commuter e) = size e.
  Proof.
    induction e.
    simpl.
    reflexivity.
    simpl.
    rewrite IHe1.
    rewrite IHe2.
    intuition.
    simpl.
    rewrite IHe1.
    rewrite IHe2.
    intuition.
  Qed.

  Theorem commuter_inverse : forall e, commuter (commuter e) = e.
  Proof.
    induction e.
    simpl.
    reflexivity.
    simpl.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
    simpl.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
  Qed.
