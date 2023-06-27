(*
 * This is a modification of a tactic implemented for CS 598 on
 * proof automation intially.
 *)

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

(*
 * Proofs about add_left and add_right will follow more easily from induction
 * over the first and the second arguments, respectively. We will write a tactic
 * that does some of this choosing for us automatically! That way, in the style
 * of StructTact, if we change a proof that used add_left to instead use add_right,
 * we won't have to change the details of our proofs. In that way, we will make
 * our proofs more robust.
 *)

(*
 * The tactic in_reduced_f matches over a goal, finds a function f applied to arguments
 * x and y, and then applies tactical t to x, y, and the reduced f.
 *)
Ltac in_reduced_f t :=
  match goal with
  | [ |- context [ ?f ?x ?y ] ] =>
    in_reduced f ltac:(t x y)
  end.

Module V1.

(*
 * The first version of autoinduct makes some extra assumptions, but doesn't rely on
 * StructTact or anything else.
 *)
Ltac autoinduct :=
  in_reduced_f ltac:(fun x y f =>
    lazymatch f with
    | (fix f n m {struct m} := @?body f n m) =>
      induction y
    | (fix f n m {struct n} := @?body f n m) =>
      induction x
    end).

(*
 * Our proofs of add_left_O and add_right_O are identical!
 *)
Lemma add_left_O :
  forall (n : nat),
    add_left n O = n.
Proof.
  intros; autoinduct; simpl; congruence.
Qed.

Lemma add_right_O :
  forall (m : nat),
    add_right O m = m.
Proof.
  intros; autoinduct; simpl; congruence.
Qed.

(*
 * Likewise for the successor case!
 *)
Lemma add_left_S :
  forall (n m : nat),
    S (add_left n m) = add_left n (S m).
Proof.
  intros; autoinduct; simpl; congruence.
Qed.

Lemma add_right_S :
  forall (n m : nat),
    S (add_right n m) = add_right (S n) m.
Proof.
  intros; autoinduct; simpl; congruence.
Qed.

(*
 * For add_right_comm and add_left_comm, the only thing that changes is
 * which lemmas we apply:
 *)
Lemma add_left_comm:
  forall (n m : nat),
    add_left n m = add_left m n.
Proof.
  intros; autoinduct; simpl.
  - symmetry. apply add_left_O.
  - find_higher_order_rewrite. apply add_left_S.
Qed.

Lemma add_right_comm:
  forall (n m : nat),
    add_right n m = add_right m n.
Proof.
  intros; autoinduct; simpl.
  - symmetry. apply add_right_O.
  - find_higher_order_rewrite. apply add_right_S.
Qed.

End V1.

Module V2.

(*
 * Our tactic makes a whole bunch of assumptions. With StructTact we can get rid of
 * some of them.
 *)

Ltac autoinduct_body :=
  in_reduced_f ltac:(fun x y f =>
    lazymatch f with
    | (fix f n m {struct m} := @?body f n m) =>
      try (rememberNonVars y); generalizeEverythingElse y; induction y
    | (fix f n m {struct n} := @?body f n m) =>
      try (rememberNonVars x); generalizeEverythingElse x; induction x
    end).

Ltac autoinduct := intros; autoinduct_body.

Lemma add_right_comm:
  forall (n m : nat),
    add_right n m = add_right m n.
Proof.
  autoinduct; intros; simpl.
  - symmetry. apply add_right_O.
  - find_higher_order_rewrite. apply add_right_S.
Qed.

Lemma add_left_comm:
  forall (n m : nat),
    add_left n m = add_left m n.
Proof.
  autoinduct; intros; simpl.
  - symmetry. apply add_left_O.
  - find_higher_order_rewrite. apply add_left_S.
Qed.

End V2.
