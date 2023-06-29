From Coq Require Import ZArith.
From AC Require Import Tactic.

Goal forall x y z, (x + y + - z = x + - z + y)%Z.
Proof.
intros x y z.
Z_zmodule.
Qed.
