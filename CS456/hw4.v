
(* Correctness proof of a (very) simple compiler *)

(* The purpose of this exercise is to use Coq to verify the              *)
(* correctness of a simple compiler. The source language is a single     *)
(* expression involving integer constants, variables and addition. The   *) 
(* target language is a assembly-like language with a single accumulator *)
(* and an infinite set of registers.                                     *)        

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Omega.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Open Scope string_scope. Open Scope nat_scope.


(* The following introduces useful notations and a number of helpful  *)
(* auxiliary functions.                                               *)

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x ]" := (cons x nil).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "| A |" := (length A) (at level 70).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.  Qed.

Inductive Id :=
  id : nat -> Id.

Definition beq_id x y :=
  match x,y with
    | (id n1), (id n2) => if  (eq_nat_decide n1 n2) then true else false
  end.

Theorem beq_id_refl : forall id, true = beq_id id id.
Proof.
  intros. simpl. unfold beq_id. destruct id0. destruct (eq_nat_decide n n).
  - reflexivity.
  - destruct n0. apply eq_nat_refl.
Qed.

Theorem beq_id_true_iff : forall x y : Id,
  beq_id x y = true <-> x = y.
Proof.
   intros id1 id2.
   unfold beq_id.
   destruct id1. destruct id2.
   destruct (eq_nat_decide n n0).
   - split. intros. apply eq_nat_eq in e. subst. reflexivity.
     intros. reflexivity.
   - split. intros contra. inversion contra.
     intros H. inversion H. destruct n1. subst.  apply eq_nat_refl.
Qed.

Theorem beq_id_false_iff : forall x y : Id,
  beq_id x y = false
  <-> x <> y.
Proof.
  intros x y. rewrite <- beq_id_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Theorem false_beq_id : forall x y : Id,
   x <> y
   -> beq_id x y = false.
Proof.
  intros x y. rewrite beq_id_false_iff.
  intros H. apply H. Qed.

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT : P -> reflect P true
| ReflectF : ~ P -> reflect P false.


Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros.
  split. inversion H. intros; reflexivity.
  intros. contradiction.
  intros. subst.
  inversion H. assumption.
Qed.


Lemma beq_natP : forall n m, reflect (n = m) (beq_nat n m).
Proof.
  intros n m.
  apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
Qed.

(* Registers are denoted as numbers *)

Definition reg := nat.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

(* Elements of the target memory (called cells) are either Registers            *)
(* (of which there are) an infinite number, or an Accumulator which is unique.  *)

Inductive cell : Set := (* memory cells *)
| Reg : reg -> cell
| Acc : cell.

(* The following are some useful definitions and properties about cells. *)

Definition cell_id x y :=
  match x,y with
    | Acc, Acc => true
    | (Reg r1), (Reg r2) => beq_id (id r1) (id r2)
    | _,_ => false                                    
  end.

Theorem cell_refl : forall c, true = cell_id c c.
Proof.
  intros. simpl. unfold cell_id. destruct c.
  + simpl. destruct (eq_nat_decide r r). reflexivity.
  - destruct n. apply eq_nat_refl.
  + reflexivity.
Qed.

Theorem cell_true_iff : forall x y : cell,
  cell_id x y = true <-> x = y.
Proof.
   intros x y.
   unfold cell_id.
   destruct x. destruct y.
   split.
   + unfold beq_id.
     destruct (eq_nat_decide r r0). subst. auto.
     intros. inversion H. apply eq_nat_eq in e. subst. reflexivity.
     intros. inversion H.
   + intros. unfold beq_id.
     destruct (eq_nat_decide r r0). reflexivity.
     destruct n. inversion H. apply eq_nat_refl.
   + split; intros; inversion H.
   + destruct y.
     split; intros; inversion H.
     split; reflexivity.
Qed.

Theorem cell_false_iff : forall x y : cell,
  cell_id x y = false
  <-> x <> y.
Proof.
  intros x y. rewrite <- cell_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Theorem false_beq_cell : forall x y : cell,
   x <> y
   -> cell_id x y = false.
Proof.
  intros x y. rewrite cell_false_iff.
  intros H. apply H. Qed.


(* We relate cells to the values they hold using maps *)

Definition total_map (A: Type) (B: Type) := A -> B.

Definition t_empty {A:Type} {B:Type} (v : B) : total_map A B :=
  (fun _ => v): A -> B.

Definition total_cell_map (A:Type) := total_map cell A.

Definition t_update {A:Type} (m : total_cell_map A)
                    (x : cell) (v : A) :=
  fun x' => match (x,x') with
           | (Acc,Acc) => v
           | ((Reg n1), (Reg n2)) => if beq_id (id n1) (id n2) then v else m x'
           | (_,_) => m x'
         end.

Lemma t_apply_empty:  forall A B x v, @t_empty A B v x = v.
Proof.
  reflexivity.
Qed.

Lemma t_update_eq : forall A (m: total_cell_map A) x v,
  (t_update m x v) x = v.
Proof.
  intros. unfold t_update. destruct x.
  - 
    rewrite <- beq_id_refl.
    reflexivity.
  - reflexivity.
Qed.
Lemma t_update_neq : forall (X:Type) v x1 x2
                         (m : total_cell_map X),
  x1 <> x2 ->
  (t_update m x1 v) x2 = m x2.
Proof.
  intros. unfold t_update.

  destruct x1. destruct x2.
  - SearchAbout beq_id.
    assert (H1: beq_id (id r) (id r0) = false). {
     apply false_beq_id.
      intro.
      inversion H0.
      auto.
    }
    rewrite H1.
    reflexivity.
  - reflexivity.
  - destruct x2.
    reflexivity.
    intuition.
Qed.

SearchAbout eq_nat_decide.

(*Lemma eqb_cell : forall (A: Type)*)

Lemma t_update_shadow : forall {A : Type} (s: total_cell_map A) v1 v2 x,
    t_update (t_update s x v1) x v2
  = t_update s x v2.
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality.
  intros.
  destruct x.
  destruct x0.
  - 
    assert (H: id r <> id r0). {
      intuition.
      admit.
    }
    assert (H1: beq_id (id r) (id r0) = false). {
      SearchAbout beq_id.
      apply false_beq_id.
      apply H.
    }
    rewrite H1.
    reflexivity.
  - reflexivity.
  - destruct x0.
    reflexivity.
    reflexivity.
Admitted.

(* The syntax of the source language.  An expression is either a constant,    *)
(* a "bind" expression that binds an identifier to a value, and evaluates an  *)
(* expression in the context of that binding, an addition operation, and a    *)
(* derf constructor that returns the value of its identifier                   *)

Inductive expr : Set :=
|const : nat -> expr
|bind : Id -> expr -> expr -> expr
|add : expr -> expr -> expr
|deref : Id -> expr.

(* The semantics of the source language *)

(* The state is an environment that maps identifiers to values - *)
(* in this language all values are numbers                       *)

Definition state := total_map Id  nat.
    
Definition empty_state := @t_empty Id nat 0.

Definition state_update (st : state) (x : Id) (v : nat) :=
  fun x' =>  if beq_id x x' then v else st x'.

Lemma state_update_eq : forall (st: state) x v,
  (state_update st x v) x = v.
Proof.
  intros. unfold t_update. destruct x. unfold state_update.
  rewrite <- beq_id_refl. reflexivity.
Qed.  

Lemma state_update_neq : forall v x1 x2 (st : state),
  x1 <> x2 ->
  (state_update st x1 v) x2 = st x2.
Proof.
  intros.
  unfold state_update.
  destruct x1. destruct x2.
  simpl.  destruct (eq_nat_decide n n0).
  +  apply eq_nat_eq in e. subst. intuition.
  + reflexivity.
Qed.


(* E is an interpreter for our source language - given a state   *)
(* and an expression, it returns the result of evaluating the    *)
(* expression in the context of that state.                      *)

Fixpoint E (s : state) (e : expr) {struct e} : nat  :=
match e with
  |const n => n
  |deref x => (s x)
  |bind x e1 e2 => E (fun y => if (beq_id x y) then (E s e1) else (s y)) e2
  |add e1 e2 => match (E s e1) with
                 | v1 => match (E s e2) with
                                | v2 => v1+v2
                             end
               end
end.

(* The target language manipulates an infinite set of registers and  *)
(* the accumulator                                                   *)

(* Specifically, 
   -  LI n loads the immediate value n in the accumulator;
   -  LOAD r loads the contents of register r in the accumulator; 
   -  STO r stores the contents of the accumulator in register r; 
   -  ADD r adds the contents of register r to the accumulator.
*)

Inductive instr : Set :=
|LI : nat -> instr
|LOAD : reg -> instr
|STO : reg -> instr
|ADD : reg -> instr
.

(* semantics of the target language *)

Definition store := total_map cell nat.

Definition update (s : store) (c : cell) (v : nat) :=
  t_update s c v.
    
Definition empty_store := @t_empty cell nat 0.

Definition store_lookup (s : store) (c : cell) := (s c).

(* Si defines an interpreter for target instructions, returning *)
(* a new store after the instruction has been evaluated in the  *)
(* context of the store argument provided.                      *)

Definition Si (s : store) (i : instr) : store :=
  match i with
  | LI n => update s Acc n
  | LOAD r => update s Acc (s (Reg r))
  | STO r => update s (Reg r) (s Acc)
  | ADD r => update s Acc (s (Reg r) + s Acc)
  end.

(* Sl generalizes Si to operate over a list of instructions  *)
Fixpoint Sl (s : store) (l : list instr) {struct l} : store :=
  match l with
  | nil => s
  | i :: l' => Sl (Si s i) l'
  end.

(* the compiler *)

(* A symbol table is a map that relates identifiers and registers *)

Definition symt := total_map Id reg.

Definition empty_symt := @t_empty Id reg 0 .

Definition symt_update (m : symt) (x : Id) (r : reg) :=
  fun (x' : Id) => if beq_id x x' then r else m x'.

Definition symt_lookup (m : symt) (x : Id) := (m x).

Lemma symt_update_eq : forall (m: symt) x r,
  symt_update m x r x = r.
Proof.
  intros.
  unfold symt_update.
  assert (H1: beq_id x x = true). {
    SearchAbout beq_id.
    symmetry.
    apply beq_id_refl.
  }
  rewrite H1.
  reflexivity.
Qed.


Lemma symt_update_neq : forall v x1 x2 (m : symt),
  x1 <> x2 ->
  (symt_update m x1 v) x2 = m x2.
Proof.
  intros.
  unfold symt_update.
  assert (H1: beq_id x1 x2 = false). {
    SearchAbout beq_id.
    apply false_beq_id.
    apply H.
  } 
  rewrite H1.
  reflexivity.
Qed.

Definition list1 (i : instr) := i :: nil.

(* The compiler:
   Let e be an expression and m an assignment from its variables
   to registers. Assume r to be a register  whose id is greater 
   than those used in m for the variables of e. Then the compilation 
   of e is a list of instructions Cr(e) defined as follows:    *)

(*     C(n) =            LI n                                      *)
(*     C(x) =            LOAD m(x)                                 *)
(*     C(e1+e2) =        C_r(e1) ++ STO r ++ C_(r+1)(e2) ++ ADD r  *)

(* When this list of instructions is executed, it stops with the value of e in 
   the accumulator. You need to define the compilation scheme for bind.        *)

Fixpoint C (m : symt) (r : reg) (e : expr)  {struct e} : list instr :=
  match e with
  | const n => list1 (LI n)
  | deref s => list1 (LOAD (m s))
  | add e1 e2 => (C m r e1 ++ list1 (STO r)) ++ C m (S r) e2 ++ list1 (ADD r)
  | bind s e1 e2 => 
    match e1 with
    | const n => (list1 (LI n)) ++ list1 (LOAD (m s))
    | deref s2 => (list1 (LOAD (m s2))) ++ list1 (LOAD (m s))
    | add e2 e3 => ((C m r e1 ++ list1 (STO r)) ++ C m (S r) e2 ++ list1 (ADD r)) ++ list1 (LOAD (m s))
    | bind s2 e3 e4 => C m r e1
    end
end.

Lemma Sl_append :
 forall (l1 l2 : list instr) (s : store), Sl s (l1 ++ l2) = Sl (Sl s l1) l2.
  induction l1.
  - simpl. intuition.
  - simpl. intuition.
Qed.

Lemma Sl_update:
    (forall (e : expr) (m : symt) (s : store) (r r' r'' : reg) (v : nat),
       r' < r /\ r' < r''  ->
       Sl (t_update s (Reg r'') v) (C m r e) (Reg r')  =
       s (Reg r')).
Proof.
  intuition.
  destruct r'.
  unfold t_update.
  Admitted.

Lemma Sl_invariant :
  forall (m : symt) (e : expr) (r r' : nat),
    r' < r ->
    forall s : store, Sl s (C m r e) (Reg r') = s (Reg r').
Proof.
  induction e.
  - simpl.
    intros.
    unfold update.
    unfold t_update.
    reflexivity.
  - 
  Admitted.

Theorem correctness :
   forall (e : expr) (m : symt) (s : store) (st : state) (r : reg),
     (forall (v : Id), (m v) < r) ->
     (forall (v : Id), st v = s (Reg (m v))) ->
     Sl s (C m r e) Acc = E st e.
Proof.
  intros.
  induction e.
  - simpl.
    unfold update.
    unfold t_update.
    reflexivity.
  - admit.
  - simpl.
    admit.
  - simpl.
    unfold update.
    unfold t_update.
    rewrite H0.
    reflexivity.
  Admitted.
