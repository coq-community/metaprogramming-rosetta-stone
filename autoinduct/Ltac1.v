(*
 * This is a modification of a tactic implemented for CS 598 on
 * proof automation intially.
 *
 * The biggest limitation of the Ltac approach is that we must limit
 * the number of arguments we can apply it to. We can't easily build
 * a version of this tactic that works on arbitrarily many arguments.
 *
 * We'll build on some tactics from StructTact, and also build a new tactic
 * in the style of StructTact. This imports the StructTact library so we can do that:
 *)
Require Import StructTact.StructTactics.

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

Ltac in_reduced f t :=
  let f_red := eval red in f in (* reduce f, but leave goal alone *)
  ltac:(t f_red).               (* run the next tactic on f_red *)

(*
 * The tactic in_reduced_f matches over a goal, finds a function f applied to arguments
 * x and y, and then applies tactical t to x, y, and the reduced f.
 *
 * Here the limitations of Ltac really shine. I stop at 3 arguments
 * because I'm impatient and I'm stuck handling each number of arguments
 * separately because of Ltac.
 *)
Ltac in_reduced_f f t :=
  match goal with
  | [ |- context [ f ?x ?y ?z ] ] =>
    in_reduced f ltac:(t x y z)
  | [ |- context [ f ?x ?y ] ] =>
    in_reduced f ltac:(t x y)
  | [ |- context [ f ?x ] ] =>
    in_reduced f ltac:(t x) 
  end.

Module V1.

(*
 * The first version of autoinduct makes some extra assumptions, but doesn't rely on
 * StructTact or anything else.
 *)
Ltac autoinduct1 f :=
  in_reduced_f f ltac:(fun x f =>
    lazymatch f with
    | (fix f n {struct n} := @?body f n) =>
      induction x
    end).

Ltac autoinduct2 f :=
  in_reduced_f f ltac:(fun x y f =>
    lazymatch f with
    | (fix f n m {struct m} := @?body f n m) =>
      induction y
    | (fix f n m {struct n} := @?body f n m) =>
      induction x
    end).

Ltac autoinduct3 f :=
  in_reduced_f f ltac:(fun x y z f =>
    lazymatch f with
    | (fix f n m p {struct p} := @?body f n m p) =>
      induction z
    | (fix f n m p {struct m} := @?body f n m p) =>
      induction y
    | (fix f n m p {struct n} := @?body f n m p) =>
      induction x
    end).

Ltac autoinduct f := first [autoinduct1 f | autoinduct2 f | autoinduct3 f]. 

(* --- Some tests --- *) 

Lemma add_left_O :
  forall (n : nat),
    add_left n O = n.
Proof.
  intros; autoinduct add_left; simpl; congruence.
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
  - find_higher_order_rewrite. apply add_left_S.
Qed.

Lemma add_right_comm:
  forall (n m : nat),
    add_right n m = add_right m n.
Proof.
  intros; autoinduct add_right; simpl.
  - symmetry. apply add_right_O.
  - find_higher_order_rewrite. apply add_right_S.
Qed.

End V1.

Import V1.

Module V2.

(*
 * Our tactic makes a whole bunch of assumptions. With StructTact we can get rid of
 * some of them.
 *)

Ltac autoinduct1 f :=
  in_reduced_f f ltac:(fun x f =>
    lazymatch f with
    | (fix f n {struct n} := @?body f n) =>
      try (rememberNonVars x); generalizeEverythingElse x; induction x
    end).

Ltac autoinduct2 f :=
  in_reduced_f f ltac:(fun x y f =>
    lazymatch f with
    | (fix f n m {struct m} := @?body f n m) =>
      try (rememberNonVars y); generalizeEverythingElse y; induction y
    | (fix f n m {struct n} := @?body f n m) =>
      try (rememberNonVars x); generalizeEverythingElse x; induction x
    end).

Ltac autoinduct3 f :=
  in_reduced_f f ltac:(fun x y z f =>
    lazymatch f with
    | (fix f n m p {struct p} := @?body f n m p) =>
      try (rememberNonVars z); generalizeEverythingElse z; induction z
    | (fix f n m p {struct m} := @?body f n m p) =>
      try (rememberNonVars y); generalizeEverythingElse y; induction y
    | (fix f n m p {struct n} := @?body f n m p) =>
      try (rememberNonVars x); generalizeEverythingElse x; induction x
    end).

Ltac autoinduct f := intros; first [autoinduct1 f | autoinduct2 f | autoinduct3 f].

Lemma add_right_comm:
  forall (n m : nat),
    add_right n m = add_right m n.
Proof.
  autoinduct add_right; intros; simpl.
  - symmetry. apply add_right_O.
  - find_higher_order_rewrite. apply add_right_S.
Qed.

Lemma add_left_comm:
  forall (n m : nat),
    add_left n m = add_left m n.
Proof.
  autoinduct add_left; intros; simpl.
  - symmetry. apply add_left_O.
  - find_higher_order_rewrite. apply add_left_S.
Qed.

End V2.


