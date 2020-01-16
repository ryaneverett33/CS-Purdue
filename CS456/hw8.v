Set Warnings "-notation-overridden,-parsing".
Add LoadPath "Purdue\CS456\Volume 2\" as PLF.
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.


Inductive ty : Type :=
  | Bool  : ty
  | Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | var x' =>
      if eqb_string x x' then s else t
  | abs x' T t1 =>
      abs x' T (if eqb_string x x' then t1 else ([x:=s] t1))
  | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)
  | tru =>
      tru
  | fls =>
      fls
  | test t1 t2 t3 =>
      test ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Inductive substi (s : tm) (x : string) : tm -> tm -> Prop :=
  | s_var1 :
      substi s x (var x) s
  | s_var2:
      forall y : string, x <> y -> substi s x (var y) (var y)
  | s_tru:
      substi s x tru tru
  | s_fls:
      substi s x fls fls
  | s_abs1:
      forall T body, substi s x (abs x T body) (abs x T body)
  | s_abs2:
      forall y T body body', x <> y -> substi s x body body' ->
          substi s x (abs y T body) (abs y T body')
  | s_app : 
      forall operator operator' operand operand',
          substi s x operator operator' -> substi s x operand operand' ->
          substi s x (app operator operand) (app operator' operand')
  | s_test :
      forall b b' t t' f f',
          substi s x b b' -> substi s x t t' -> substi s x f f' ->
          substi s x (test b t f) (test b' t' f')
.

Hint Constructors substi.

Lemma subst_substi : forall s x t t', 
  [x := s]t = t' -> substi s x t t'.
Proof with auto.
  (*
  induction t; simpl; intros; rewrite <- H.
  - destruct (eqb_string x s0) eqn: E.
    + SearchAbout eqb_string.
      apply eqb_string_true_iff in E.
      apply s_var1.
apply eqb_eq in E.
    admit.
    (*+ apply eqb_eq in E. subst.
      apply s_var1.
    + apply s_var2.
      now apply eqb_neq.*)
    SearchAbout eqb_string.
    (* Remember tactic https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.remember *)
  - *)
    intros.
    generalize dependent t'.
    induction t.
    simpl. remember (eqb_string x s0) as eqb1;
    symmetry in Heqeqb1;
    destruct eqb1.
    apply eqb_string_true_iff in Heqeqb1.
    intros; subst; auto.
    apply eqb_string_false_iff in Heqeqb1.
    intros; subst; auto.
    intros; subst; try constructor; auto.
    simpl. remember (eqb_string x s0) as eqb1;
    symmetry in Heqeqb1;
    destruct eqb1.
    apply eqb_string_true_iff in Heqeqb1.
    intros. subst. auto.
    apply eqb_string_false_iff in Heqeqb1.
    intros. subst. auto.
    intros; subst; try constructor; auto.
    intros; subst; try constructor; auto.
    intros; subst; try constructor; auto.
  Qed.

Lemma substi_subst : forall s x t t',
  substi s x t t' -> [x := s]t = t'.
Proof with auto.
  intros.
  induction H; simpl; auto;
    try rewrite <- eqb_string_refl; auto;
    try rewrite false_eqb_string; subst; auto.
Qed.

Theorem substi_correct : forall s x t t',
  [x:=s]t = t' <-> substi s x t t'.
Proof.
  intros. split.
  - apply subst_substi.
  - apply substi_subst.
Qed.