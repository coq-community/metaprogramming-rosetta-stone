Require Import Loader.

(*
 * We are going to use our tactics to write proofs about the natural numbers.
 * To avoid using Coq's lemmas by accident, though, we're going to define our own
 * version of the Nat datatype:  
 *)
Inductive nat : Set :=
| O : nat
| S : nat -> nat.

(*
 * To start, we will define an addition function two ways, one recursing
 * on the first argument:
 *)
Fixpoint add_left (n m : nat) : nat :=
  match n with
  | O => m
  | S p => S (add_left p m)
  end.

(*
 * And one recursing on the second argument:
 *)
Fixpoint add_right (n m : nat) : nat :=
  match m with
  | O => n
  | S p => S (add_right n p)
  end.

(* --- Some tests --- *) 

Lemma add_left_O :
  forall (n : nat),
    add_left n O = n.
Proof.
  intros. autoinduct add_left; simpl; congruence.
Qed.

Lemma add_right_O :
  forall (m : nat),
    add_right O m = m.
Proof.
  intros; autoinduct add_right; simpl; congruence.
Qed.

Lemma add_left_S :
  forall (n m : nat),
    S (add_left n m) = add_left n (S m).
Proof.
  intros; autoinduct add_left; simpl; congruence.
Qed.

Lemma add_right_S :
  forall (n m : nat),
    S (add_right n m) = add_right (S n) m.
Proof.
  intros; autoinduct add_right; simpl; congruence.
Qed.

Lemma add_left_comm:
  forall (n m : nat),
    add_left n m = add_left m n.
Proof.
  intros; autoinduct add_left; simpl.
  - symmetry. apply add_left_O.
  - rewrite IHn0. apply add_left_S.
Qed.

Lemma add_right_comm:
  forall (n m : nat),
    add_right n m = add_right m n.
Proof.
  intros; autoinduct add_right; simpl.
  - symmetry. apply add_right_O.
  - rewrite IHn0. apply add_right_S.
Qed.

