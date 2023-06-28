From elpi Require Import elpi.
From Autoinduct Require Import Autoinduct.

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

Lemma add_left_O : forall (n : nat), add_left n O = n.
Proof.
  intros.
  (* autoinduct on (add_left n O). *)
  (* autoinduct on add_left. *)
  autoinduct.
  all: (simpl; congruence).
Qed.
 
Lemma add_right_O : forall (m : nat), add_right O m = m.
Proof.
  intros.
  (* autoinduct on (add_right O m). *)
  (* autoinduct on add_right. *)
  autoinduct.
  all: (simpl; congruence).
Qed.
 
Lemma add_left_S : forall (n m : nat), S (add_left n m) = add_left n (S m).
Proof.
  intros.
  (* autoinduct on (add_left n m). *)
  (* autoinduct on add_left. *)
  autoinduct.
  all: (simpl; congruence).
Qed.
 
Lemma add_right_S : forall (n m : nat), S (add_right n m) = add_right (S n) m.
Proof.
  intros.
  (* autoinduct on (add_right n m). *)
  (* autoinduct on add_right. *)
  autoinduct.
  all: (simpl; congruence).
Qed.
 
Lemma add_left_comm : forall (n m : nat), add_left n m = add_left m n.
Proof.
  intros.
  (* autoinduct on (add_left n m). *)
  (* autoinduct on add_left. *)
  autoinduct.
  all: simpl.
  - symmetry. apply add_left_O.
  - rewrite IHn. apply add_left_S.
Qed.

Lemma add_right_comm : forall (n m : nat), add_right n m = add_right m n.
Proof.
  intros.
  (* autoinduct on (add_right n m). *)
  (* autoinduct on add_right. *)
  autoinduct.
  all: simpl.
  - symmetry. apply add_right_O.
  - rewrite IHm. apply add_right_S.
Qed.
