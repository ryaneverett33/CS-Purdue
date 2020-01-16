Add LoadPath "Purdue\CS456\Book".
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Maps.
Export List ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Set Implicit Arguments.

Notation var := string.
Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.

Infix "==v" := var_eq (no associativity, at level 50).

(* In this problem set, we'll expand on our understanding of *)
(* arithmetic expressions. *)

Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

(* Our first exercise is to write an interpreter for this language *)
(* A valuation represents a mapping between variables and their values *)

(* Valuations are implemented as partial maps - see *)
(*     https://softwarefoundations.cis.upenn.edu/lf-current/Maps.html *)
(* for an explanation of how partial maps are defined *)

(* You'll need to compile Maps.v and make sure the compiled file is in the *)
(* same directory (or in a path Coq knows about) as this file *)

Definition valuation := partial_map nat.

Fixpoint interp (e : arith) (m : valuation) : nat :=
    match e with
  | Const n => n
  | Var x  =>
    match (m x)  with
    | None => 0 (* goofy default value! *)
    | Some n => n
    end
  | Plus e1 e2 => interp e1 m + interp e2 m
  | Minus e1 e2 => interp e1 m - interp e2 m
                   (* For anyone who's wondering: this [-] sticks at 0,
                    * if we would otherwise underflow. *)
  | Times e1 e2 => interp e1 m * interp e2 m
  end.

Check arith.

(* Here's the transformation we defined last time. *)
Fixpoint commuter (e : arith) : arith :=
  match e with
  | Const _ => e
  | Var _ => e
  | Plus e1 e2 => Plus (commuter e2) (commuter e1)
  | Minus e1 e2 => Minus (commuter e1) (commuter e2)
                   (* ^-- NB: didn't change the operand order here! *)
  | Times e1 e2 => Times (commuter e2) (commuter e1)
  end.

Theorem commuter_test : commuter (Var "x") = (Var "x").
  simpl.
  reflexivity.
Qed.

(* Instead of proving various odds-and-ends properties about it,
 * let's show what we *really* care about: it preserves the
 * *meanings* of expressions! *)
Theorem commuter_ok : forall v e, interp (commuter e) v = interp e v.
Proof.
  induction e.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  simpl; rewrite IHe1, IHe2; intuition.
  simpl; rewrite IHe1, IHe2; intuition.
  simpl; rewrite IHe1, IHe2; intuition.
Qed.

(* Next, we will consider compiling this language to a simple
   stack machine which supports the following instructions *) 

Locate "++".

Inductive instruction :=
| PushConst (n : nat)
| PushVar (x : var)
| Add
| Subtract
| Multiply.

(* The behavior of the machine is straightforward: binary arithmetic 
 * operations pop their arguments off the stack, compute the result, and 
 * return a new stack with this result at the top.  *)

(* The run1 function computes how to execute a single instruction given a 
 * mapping of variables to values (v) and a stack (represented as a list of numbers) *)

Definition run1 (i : instruction) (v : valuation) (stack : list nat) : list nat :=
   match i with
  | PushConst n => n :: stack
  | PushVar x => 
    (match (v x) with
    | None => 0
    | Some n => n
    end) :: stack
  | Add => 
    match stack with
    | x :: y :: stack => (x + y) :: stack
    | _ => stack
    end
  | Subtract =>
    match stack with
    | x :: y :: stack => (x - y) :: stack
    | _ => stack
    end
  | Multiply => 
    match stack with
    | x :: y :: stack => (x * y) :: stack
    | _ => stack
    end
  end.

(* Here's how to run several instructions. *)
Fixpoint run (is : list instruction) (v : valuation) (stack : list nat) : list nat :=
  match is with
  | nil => stack
  | i :: is' => run is' v (run1 i v stack)
  end.

(* Now, we can directly compile an arithmetic expression to an equivalent stack program *)
Fixpoint compile (e : arith) : list instruction :=
  match e with
  | Const a => PushConst a :: nil
  | Var a => Add :: PushVar a :: nil
  | Plus a b => compile (a) ++ compile(b) ++ Add :: nil
  | Minus a b => compile (a) ++ compile (b) ++ Subtract :: nil
  | Times a b => compile (a) ++ compile (b) ++ Multiply :: nil
  end.

(* Finally, we would like to prove that the values produced by interpreting arithmetic 
 * expressions are the same as the result of compiling these expressions to the stack   
 * machine and running the compiled version.                                           *)

(* Here is a useful lemma that will help the proof. *)
(* Hint: app_assoc_reverse will be useful here *)
SearchAbout "app_assoc_reverse".
SearchAbout "app_assoc".
SearchAbout "_ ++ _".

(*app_assoc_reverse:
  forall (A : Type) (l m n : list A), ((l ++ m) ++ n)%list = (l ++ m ++ n)%list*)
Lemma compile_ok' : forall e v is stack, run (compile e ++ is) v stack = run is v (interp e v :: stack).
Proof.
  induction e.
  simpl.
  reflexivity.
  2: {
    simpl.
    intros.
    rewrite app_assoc_reverse.
    rewrite IHe1.
    rewrite app_assoc_reverse.
    rewrite IHe2.
    simpl.
    assert (H: interp e1 v + interp e2 v = interp e2 v + interp e1 v). {
      intuition.
    }
    rewrite H.
    reflexivity.
  }
  3: {
    simpl.
    intros.
    rewrite app_assoc_reverse.
    rewrite IHe1.
    rewrite app_assoc_reverse.
    rewrite IHe2.
    simpl.
    assert (H: interp e1 v * interp e2 v = interp e2 v * interp e1 v). {
      intuition.
    }
    rewrite H.
    reflexivity.
  }
  2: {
    simpl.
    intros.
    rewrite app_assoc_reverse.
    rewrite IHe1.
    rewrite app_assoc_reverse.
    rewrite IHe2.
    simpl.
    admit.
    (*
      run is v (interp e2 v - interp e1 v :: stack) =
      run is v (interp e1 v - interp e2 v :: stack)
    *)
  }
  1: {
    (*forall (v : valuation) (is : list instruction) (stack : list nat),
run (compile (Var x) ++ is) v stack = run is v (interp (Var x) v :: stack)*)
    
    (*simpl. breaks down to function definition *)
    admit.
  }
  (* rewrite (app_assoc_reverse (compile (Var x)) (is)). *)
Admitted.

(* The overall theorem follows as a simple corollary. *)
Theorem compile_ok : forall e v, run (compile e) v nil = interp e v :: nil.
Proof.
  intros.
  rewrite (app_nil_end (compile e)).
  apply compile_ok'.
Qed.



