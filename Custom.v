(*
 * CS 598 TLR
 * Artifact 4: Custom Tactics in Ltac
 * Talia's Copy
 *
 * READ ME FIRST: As always, here you are graded for the discussion
 * question at the bottom of this file, and not on your ability to finish the proofs.
 *
 * At the end of this class (or, if you're not attending in person,
 * sometime before 1230 PM the day of class) you'll post on the forum
 * about what you found challenging, what you enjoyed, how the experience
 * compared to the experience from last week, and how you wish you could
 * improve the automation to make the experience better. 
 * If you or someone you're working with is a Coq wizard already,
 * and you know about automation that already exists that makes the
 * job easy, definitely take note of that and mention it as well.
 *
 * If you have a lot of trouble with a proof, it's OK to ask me for help
 * (or click the "ask for help" button on Zoom if you're not here in person).
 * It's also OK to ask people in other groups.
 *
 * But again, as before, this is about the journey, not the destination.
 *)

(*
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
 *
 * But before we get there, let's write a couple of proofs that show this symmetry.
 *)

(* --- PART 1 : Symmetry of Induction --- *)

Module Part1.

(*
 * When we change which argument we recurse over, going between add_left and add_right
 * above, our proofs change in a way that reflects that.
 *
 * For example, the proofs we get definitionally will change, to start.
 * For add_left, for any m, add_left 0 m = m follows by reflexivity;
 * for add_right, for any n, add_right n 0 = n follows by reflexivity.
 *
 * If we look at the more difficult direction for each---the propositional one---the 
 * symmetry is reflected in which argument we induct over. That is,
 * for add_left, for any n, add_left n 0 = n follows by induction on n;
 * for add_right, for any m, add_right 0 m = m follows by induction on m.
 * I'll show these two proofs (a bit manually so you can step through them):
 *)
Lemma add_left_O :
  forall (n : nat),
    add_left n O = n.
Proof.
  induction n; simpl.         (* induct over n, then simplify goal *)
  - reflexivity.              (* base case by reflexivity *)
  - rewrite IHn. reflexivity. (* inductive case by the inductive hypothesis *)
Qed.

Lemma add_right_O :
  forall (m : nat),
    add_right O m = m.
Proof.
  induction m; simpl.         (* induct over m, then simplify goal *)
  - reflexivity.              (* base case by reflexivity *)
  - rewrite IHm. reflexivity. (* inductive case by the inductive hypothesis *)
Qed.

(*
 * As you can see, the proofs are very similar, and differ only in which argument
 * we induct over (and the name of the inductive hypothesis we rewrite by---IHn or IHm).
 * When we look at the successor case, something similar happens---but you'll show it :).
 * I'll prove add_left_S, and you'll prove add_right_S.
 *
 * Here's my proof:
 *)
Lemma add_left_S :
  forall (n m : nat),
    S (add_left n m) = add_left n (S m).
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

(*
 * EXERCISE 1: Prove add_right_S.
 *)
Lemma add_right_S :
  forall (n m : nat),
    S (add_right n m) = add_right (S n) m.
Proof.
  induction m; intros; simpl.
  - reflexivity.
  - rewrite IHm. reflexivity.
Qed.

(*
 * Commutativity of addition follows by these lemmas, and is similarly symmetric.
 * I'll prove left addition commutative; you'll prove right addition commutative.
 * Here's my proof:
 *)
Lemma add_left_comm:
  forall (n m : nat),
    add_left n m = add_left m n.
Proof.
  induction n; intros; simpl.
  - symmetry. apply add_left_O.
  - rewrite IHn. apply add_left_S.
Qed.

(*
 * EXERCISE 2: Prove right addition commutative.
 *)
Lemma add_right_comm:
  forall (n m : nat),
    add_right n m = add_right m n.
Proof.
  induction m; intros; simpl.
  - symmetry. apply add_right_O.
  - rewrite IHm. apply add_right_S.
Qed.

End Part1.

(*
 * The goal for this exercise is to make proofs more robust, so that our proofs don't
 * have to change much as we switch between add_left and add_right.
 * To do that, we'll start by using some existing StructTact tactics---then
 * we'll build our own.
 *)

(* --- Part 2: Robust Proofs --- *)

Module Part2.

(*
 * We can make these proofs more robust, so that fewer things change when we move between
 * add_left and add_right. Some of this we can do without using anything fancy, just
 * using Coq's existing tactics. For example, we can dispatch the base and inductive
 * case of both proofs of the O case by using "congruence", so we no longer have to
 * change our rewrite by IHn to rewrite by IHm instead:
 *)
Lemma add_left_O :
  forall (n : nat),
    add_left n O = n.
Proof.
  induction n; simpl; congruence.
Qed.

Lemma add_right_O :
  forall (m : nat),
    add_right O m = m.
Proof.
  induction m; simpl; congruence.
Qed.

(*
 * Similarly for the successor case:
 *)
Lemma add_left_S :
  forall (n m : nat),
    S (add_left n m) = add_left n (S m).
Proof.
  induction n; intros; simpl; congruence.
Qed.

Lemma add_right_S :
  forall (n m : nat),
    S (add_right n m) = add_right (S n) m.
Proof.
  induction m; intros; simpl; congruence.
Qed.

(*
 * But this doesn't help us with commutativity. We can make our proofs of add_left_comm 
 * and add_right_comm a bit more robust with StructTact, though!
 * StructTact has a tactic called "find_higher_order_rewrite", which searches for
 * a relevant hypothesis to rewrite by. You can use this tactic to write a proof
 * that doesn't refer at all to "IHn" or "IHm". Give it a try.
 *
 * EXERCISE 3: Use "find_higher_order_rewrite" from StructTact to write proofs
 * of add_left_comm and add_right_comm that don't refer at all to "IHn" or "IHm".
 *)
Lemma add_left_comm:
  forall (n m : nat),
    add_left n m = add_left m n.
Proof.
  induction n; intros; simpl.
  - symmetry. apply add_left_O.
  - find_higher_order_rewrite. apply add_left_S.
Qed.

Lemma add_right_comm:
  forall (n m : nat),
    add_right n m = add_right m n.
Proof.
  induction m; intros; simpl.
  - symmetry. apply add_right_O.
  - find_higher_order_rewrite. apply add_right_S.
Qed.

End Part2.

(*
 * Next, we will write our own structural tactic that abstracts over induction,
 * so that we can remove "induction n" and "induction m". We'll call this "autoinduct".
 * Our tactic "autoinduct" will look at our goal, unfold our addition function,
 * and figure out which argument it's recursing over. It will then decide which
 * argument to induct over, and run induction for us!
 *)

(* --- Part 3: Structural Tactics --- *)

Module Part3.

(*
 * Now we'll write our structural tactic for induction. I'll walk through smaller pieces
 * of this, since Ltac can be really confusing when we're starting off.
 *
 * Our structural tactic for induction is going to need to unfold or addition
 * function to figure out what it inducts over. But in doing so, we don't want
 * it to change our goal. We can do this in Ltac as follows:
 *)
Lemma demo_1 :
  forall (n : nat),
    add_left n O = n.
Proof.
  intros.                                     (* goal : add_left n O = n *)  
  let add_left_red := eval red in add_left in (* reduce add_left, but leave goal alone *)
  idtac add_left_red.                         (* print the result *)
  admit.
Abort.

(*
 * If you look, you can see it printing the definition of add_left in the "messages"
 * buffer on the right of your screen. Let's move this into its own tactical
 * (a tactic that takes another tactic as an argument):
 *)
Ltac in_reduced f t :=
  let f_red := eval red in f in (* reduce f, but leave goal alone *)
  ltac:(t f_red).               (* run the next tactic on f_red *)

(*
 * OK, now this behaves the same way:
 *)
Lemma demo_2 :
  forall (n : nat),
    add_left n O = n.
Proof.
  intros.                                      (* goal : add_left n O = n *)  
  in_reduced add_left ltac:(fun f => idtac f). (* print reduced add_left *)
  admit.
Abort.

(*
 * The next thing we'll need is the ability to actually find the function
 * to unfold. We can do that by pattern matching in Ltac. For example,
 * here we find a function applied to some variables in the goal, then
 * print the reduced function and its two arguments:
 *)
Lemma demo_3 :
  forall (n : nat),
    add_left n O = n.
Proof.
  intros.                          (* goal : add_left n O = n *)
  match goal with                  (* match on the goal *)
  | [ |- context [ ?f ?x ?y ] ] => (* look for a function applied to two arguments *)
    in_reduced f ltac:(fun f => idtac f; idtac x; idtac y) (* print reduced f and args *)
  end.
  admit.
Abort.

(*
 * EXERCISE 4: By pulling out and generalizing the script above, fill in the tactic
 * in_reduced_f below, which matches over a goal, finds a function f applied to arguments
 * x and y, and then applies tactical t to x, y, and the reduced f. If successful,
 * test_1 should print the same thing as demo_3.
 *)
Ltac in_reduced_f t :=
  match goal with
  | [ |- context [ ?f ?x ?y ] ] =>
    in_reduced f ltac:(t x y)
  end.

(*
 * The test that should print the same thing as demo_3:
 *)
Lemma test_1 :
  forall (n : nat),
    add_left n O = n.
Proof.
  intros.
  in_reduced_f ltac:(fun x y f => idtac f; idtac x; idtac y).
  admit.
Abort.

(*
 * OK, the next thing we'll need is a way to look inside of that add_left definition
 * (or whatever function f we've unfolded) and find the argument it recurses over.
 * If we look at our definition of add_left that test_1 prints above, we see this:
 *
 * (fix add_left (n m : nat) {struct n} : nat :=
 *  match n with
 *  | O => m
 *  | S p => S (add_left p m)
 *  end)
 *
 * The "struct n" there means that it's recursing and decreasing over n, so we can
 * use that to tell. So here is some Ltac that prints which argument it recurses over:
 *)
Ltac which_argument :=
  in_reduced_f ltac:(fun x y f =>
    lazymatch f with
    | (fix f n m {struct m} := @?body f n m) =>
      idtac "second argument"
    | (fix f n m {struct n} := @?body f n m) =>
      idtac "first argument"
    end).

(*
 * Which is the first argument for add_left:
 *)
Lemma demo_4 :
  forall (n : nat),
    add_left n O = n.
Proof.
  intros.
  which_argument. (* first argument *)
  admit.
Abort.

(*
 * And the second argument for add_right:
 *)
Lemma demo_5 :
  forall (m : nat),
    add_right O m = m.
Proof.
  intros.
  which_argument. (* second argument *)
  admit.
Abort.

(*
 * EXERCISE 5: Modify which_argument to implement print_argument below, which prints
 * x (the first argument to f) when f recurses over the first argument, and prints
 * y (the second argument to f) when f recurses over the second argument:
 *)
Ltac print_argument :=
  in_reduced_f ltac:(fun x y f =>
    lazymatch f with
    | (fix f n m {struct m} := @?body f n m) =>
      idtac y
    | (fix f n m {struct n} := @?body f n m) =>
      idtac x
    end).

(*
 * These tests should print n and m respectively, if your implementation is correct:
 *)
Lemma test_2 :
  forall (n : nat),
    add_left n O = n.
Proof.
  intros.
  print_argument. (* n *)
  admit.
Abort.

Lemma test_3 :
  forall (m : nat),
    add_right O m = m.
Proof.
  intros.
  print_argument. (* m *)
  admit.
Abort.

(*
 * Congrats, you've now written a tactic that prints the argument to induct over. 
 * So now there's just one more step to write your first implementation of
 * autoinduct: actually induct over that argument :).
 *
 * EXERCISE 6: Fill in the code below to implement autoinduct, which inducts over 
 * x when f recurses over the first argument, and inducts over the
 * y when f recurses over the second argument.
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
 * Our proofs of add_left_O and add_right_O are now identical!
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

End Part3.

(*
 * Our tactic makes a whole bunch of assumptions. If you have time, you can break
 * and then generalize those assumptions. Otherwise, it's good to move to the discussion
 * question at the bottom.
 *)

(* --- PART 4: Bonus --- *)

(*
 * BONUS: What assumptions does your autoinduct tactic make?
 * Find some proofs that break those assumptions and cause it fail, choose
 * the wrong hypothesis, or put you in a proof state that makes it impossible
 * to prove your goal. Then, try to improve your autoinduct implementation 
 * so that it no longer makes those assumptions.
 *)

Module Part4.

Import Part3.

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

End Part4.

(* --- PART 5: Discussion --- *)

(*
 * That's it for now! When we have 25 minutes left of class, please do this:
 *
 *  1. Turn to your group and discuss the question below.
 *  2. Post your answer─just one answer for your group, clearly indicating
 *     all members of the group. (If you are not here, and are working alone,
 *     you can post your answer alone.)
 *  3. With 10 minutes left, finish posting your answer, so we can discuss
 *     a bit as a class.
 *
 * You'll be graded based on whether you post an answer, not based on
 * what it is, so don't worry too much about saying something silly.
 *
 * DISCUSSION QUESTION: What was it like writing structural tactics?
 * Do you think this is an approach you would take to making proofs more robust
 * to changes? What do you think the challenges are of taking this approach,
 * and what if anything are the tradeoffs of doing so relative to using
 * more traditional tactics? What would you do differently?
 *)
