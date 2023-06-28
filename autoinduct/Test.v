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
  autoinduct on (add_left n O) || (idtac "step0 fails"; induction n).
  all: (simpl; congruence).
Qed.
 
Lemma add_right_O : forall (m : nat), add_right O m = m.
Proof.
  intros.
  autoinduct on (add_right O m) || (idtac "step0 fails"; induction m).
  all: (simpl; congruence).
Qed.

End Step0.

Module Step1.

Lemma add_left_O : forall (n : nat), add_left n O = n.
Proof.
  intros.
  autoinduct on add_left || (idtac "step1 fails"; induction n).
  all: (simpl; congruence).
Qed.
 
Lemma add_right_O : forall (m : nat), add_right O m = m.
Proof.
  intros.
  autoinduct on add_right  || (idtac "step1 fails"; induction m).
  all: (simpl; congruence).
Qed.

End Step1.

Module Step2.

Lemma add_left_O : forall (n : nat), add_left n O = n.
Proof.
  intros.
  autoinduct || (idtac "step2 fails"; induction n).
  all: (simpl; congruence).
Qed.
 
Lemma add_right_O : forall (m : nat), add_right O m = m.
Proof.
  intros.
  autoinduct || (idtac "step2 fails"; induction m).
  all: (simpl; congruence).
Qed.

End Step2.