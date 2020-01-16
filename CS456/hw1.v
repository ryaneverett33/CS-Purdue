From Coq Require Export String.
From Coq Require Import Bool.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  Admitted.

Theorem plus_id_example: 
forall (n m:nat), 
n = m -> 
n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite H.
  reflexivity.
  Qed.

Lemma orb_always_true :
  forall b,
    orb true b = true.
Proof. reflexivity. Qed.

(** **** Exercise: 3 stars, standard, optional (andb_eq_orb)  

    Prove the following theorem.  (Hint: This one can be a bit tricky,
    depending on how you approach it.  You will probably need both
    [destruct] and [rewrite], but destructing everything in sight is
    not the best way.) *)

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  destruct c.
  - (*b && true = b || true -> b = true*)
    rewrite andb_true_r.
    rewrite orb_true_r.
    (*b = true -> b = true*)
    intros.         (*Store that b is true*)
    assumption.     (*Match our hypothesis*)
  - (*b && false = b || false -> b = false*)
    rewrite andb_false_r.
    rewrite orb_false_r.
    (*false = b -> b = false*)
    symmetry.       (*Flip around and store*)
    assumption.     (*Match our hypothesis*)
  Qed.
(** **** Exercise: 3 stars, standard (binary)  

    We can generalize our unary representation of natural numbers to
    the more efficient binary representation by treating a binary
    number as a sequence of constructors [A] and [B] (representing 0s
    and 1s), terminated by a [Z]. For comparison, in the unary
    representation, a number is a sequence of [S]s terminated by an
    [O].

    For example:

        decimal            binary                           unary
           0                   Z                              O
           1                 B Z                            S O
           2              A (B Z)                        S (S O)
           3              B (B Z)                     S (S (S O))
           4           A (A (B Z))                 S (S (S (S O)))
           5           B (A (B Z))              S (S (S (S (S O))))
           6           A (B (B Z))           S (S (S (S (S (S O)))))
           7           B (B (B Z))        S (S (S (S (S (S (S O))))))
           8        A (A (A (B Z)))    S (S (S (S (S (S (S (S O)))))))

    Note that the low-order bit is on the left and the high-order bit
    is on the right -- the opposite of the way binary numbers are
    usually written.  This choice makes them easier to manipulate. *)

Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

(** Complete the definitions below of an increment function [incr]
    for binary numbers, and a function [bin_to_nat] to convert
    binary numbers to unary numbers. *)

Fixpoint incr (m:bin) : bin :=
  match m with
    | Z => B Z
    | B Z => A (B Z)
    | A m' => B m'
    | B m' => A (A (m'))
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
    | Z => O
    | B Z => S O
    | A (B Z) => S (S 0)
    | B (B Z) => S (S (S O))
    | A m' => S (bin_to_nat m')
    | B m' => S (bin_to_nat m')
  end.

(** The following "unit tests" of your increment and binary-to-unary
    functions should pass after you have defined those functions correctly.
    Of course, unit tests don't fully demonstrate the correctness of
    your functions!  We'll return to that thought at the end of the
    next chapter. *)

Example test_bin_incr1 : (incr (B Z)) = A (B Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr2 : (incr (A (B Z))) = B (B Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr3 : (incr (B (B Z))) = A (A (B Z)).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr3_1 : (incr (B (B (B Z)))) = A (A (B (B Z))).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr4 : bin_to_nat (A (B Z)) = 2.
Proof. simpl. reflexivity. Qed.

Example test_bin_incr5 :
        bin_to_nat (incr (B Z)) = 1 + bin_to_nat (B Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr6 :
        bin_to_nat (incr (incr (B Z))) = 2 + bin_to_nat (B Z).
Proof. simpl. reflexivity. Qed.
