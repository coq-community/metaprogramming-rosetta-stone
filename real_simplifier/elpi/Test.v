From elpi Require Import elpi.

Require Import Reals.
Require Import ZArith.
Require Import QArith.

From RealSimplify Require Import RealSimplify Theory.

Section Test.
Variable x : R.
Open Scope R.

Goal (x+(Rmax ((3*4+5^2-6)/7) (1/2)) = x + 31/7).
Proof.
  real_simplify.
  reflexivity.
Qed.

End Test.
