From Coq Require Import ZArith.
From AC Require Import Tactic.

Goal forall x y z, (x + y + - z = x + - z + y)%Z.
Proof.
intros x y z.
Z_zmodule.
Qed.

Goal forall x y y' z, y = y' -> (x + y + - z + y = x + - z + y + y')%Z.
Proof.
intros x y y' z Hy.
Z_zmodule_simplify; exact Hy.
Qed.
