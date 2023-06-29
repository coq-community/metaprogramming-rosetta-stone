From Autoinduct Require Import Autoinduct.

Set Default Proof Mode "Classic".

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.
 
Fixpoint add_left (n m : nat) : nat :=
  match n with
  | O => m
  | S p => S (add_left p m)
  end.
 
Fixpoint add_right (n m : nat) : nat :=
  match m with
  | O => n
  | S p => S (add_right n p)
  end.

Module Step0.

Lemma add_left_O : forall (n : nat), add_left n O = n.
Proof.
  intros.
  autoinduct on (add_left n O) || (idtac "step0 test1 fails"; induction n).
  all: (simpl; congruence).
Qed.
 
Lemma add_right_O : forall (m : nat), add_right O m = m.
Proof.
  intros.
  autoinduct on (add_right O m) || (idtac "step0 test2 fails"; induction m).
  all: (simpl; congruence).
Qed.

Lemma add_left_S :
  forall (n m : nat),
    S (add_left n m) = add_left n (S m).
Proof.
  intros.
  autoinduct on (add_left n m) || (idtac "step0 test3 fails"; induction n).
  all: (simpl; congruence).
Qed.

Lemma add_right_S :
  forall (n m : nat),
    S (add_right n m) = add_right (S n) m.
Proof.
  intros.
  autoinduct on (add_right n m) || (idtac "step0 test4 fails"; induction m).
  all: (simpl; congruence).
Qed.

Lemma add_left_comm:
  forall (n m : nat),
    add_left n m = add_left m n.
Proof.
  intros.
  autoinduct on (add_left n m) || (idtac "step0 test5 fails"; induction n).
  all: simpl.
  - symmetry. apply add_left_O.
  - (rewrite IHn || rewrite IHn0). apply add_left_S.
Qed.

Lemma add_right_comm:
  forall (n m : nat),
    add_right n m = add_right m n.
Proof.
  intros.
  autoinduct on (add_right n m) || (idtac "step0 test6 fails"; induction m).
  all: simpl.
  - symmetry. apply add_right_O.
  - (rewrite IHm || rewrite IHn0). apply add_right_S.
Qed.

End Step0.

Module Step1.

Lemma add_left_O : forall (n : nat), add_left n O = n.
Proof.
  intros.
  autoinduct on add_left || (idtac "step1 test1 fails"; induction n).
  all: (simpl; congruence).
Qed.
 
Lemma add_right_O : forall (m : nat), add_right O m = m.
Proof.
  intros.
  autoinduct on add_right  || (idtac "step1 test2 fails"; induction m).
  all: (simpl; congruence).
Qed.

Lemma add_left_S :
  forall (n m : nat),
    S (add_left n m) = add_left n (S m).
Proof.
  intros.
  autoinduct on add_left || (idtac "step1 test3 fails"; induction n).
  all: (simpl; congruence).
Qed.

Lemma add_right_S :
  forall (n m : nat),
    S (add_right n m) = add_right (S n) m.
Proof.
  intros.
  autoinduct on add_right || (idtac "step1 test4 fails"; induction m).
  all: (simpl; congruence).
Qed.

Lemma add_left_comm:
  forall (n m : nat),
    add_left n m = add_left m n.
Proof.
  intros.
  autoinduct on add_left || (idtac "step1 test5 fails"; induction n).
  all: simpl.
  - symmetry. apply add_left_O.
  - (rewrite IHn || rewrite IHn0). apply add_left_S.
Qed.

Lemma add_right_comm:
  forall (n m : nat),
    add_right n m = add_right m n.
Proof.
  intros.
  autoinduct on add_right || (idtac "step1 test6 fails"; induction m).
  all: simpl.
  - symmetry. apply add_right_O.
  - (rewrite IHm || rewrite IHn0). apply add_right_S.
Qed.

End Step1.

Module Step2.

Lemma add_left_O : forall (n : nat), add_left n O = n.
Proof.
  intros.
  autoinduct || (idtac "step2 test1 fails"; induction n).
  all: (simpl; congruence).
Qed.
 
Lemma add_right_O : forall (m : nat), add_right O m = m.
Proof.
  intros.
  autoinduct || (idtac "step2 test2 fails"; induction m).
  all: (simpl; congruence).
Qed.

Lemma add_left_S :
  forall (n m : nat),
    S (add_left n m) = add_left n (S m).
Proof.
  intros.
  autoinduct || (idtac "step2 test3 fails"; induction n).
  all: (simpl; congruence).
Qed.

Lemma add_right_S :
  forall (n m : nat),
    S (add_right n m) = add_right (S n) m.
Proof.
  intros.
  autoinduct || (idtac "step2 test4 fails"; induction m).
  all: (simpl; congruence).
Qed.

Lemma add_left_comm:
  forall (n m : nat),
    add_left n m = add_left m n.
Proof.
  intros.
  autoinduct || (idtac "step2 test5 fails"; induction n).
  all: simpl.
  - symmetry. apply add_left_O.
  - (rewrite IHn || rewrite IHn0). apply add_left_S.
Qed.

Lemma add_right_comm:
  forall (n m : nat),
    add_right n m = add_right m n.
Proof.
  intros.
  autoinduct || (idtac "step2 test6 fails"; induction m).
  all: simpl.
  - symmetry. apply add_right_O.
  - (rewrite IHm || rewrite IHn0). apply add_right_S.
Qed.


End Step2.