Add LoadPath "Purdue\CS456\Volume 2\".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
Require Import Hoare.
Require Import Imp.

Theorem slow_assignment : forall m,
    {{ fun st => st X = m}}
     Y ::= 0;;
     WHILE ~(X = 0) DO
       X ::= X - 1;;
       Y ::= Y + 1
     END
   {{ fun st => st Y = m}}.


Theorem slow_addition : forall m p,
  {{ fun st =>  st X = m /\ st Z = p}}
   WHILE ~(X = 0) DO
      Z ::= Z + 1;;
      X ::= X - 1
   END
   {{ fun st => st Z = p + m}}.


