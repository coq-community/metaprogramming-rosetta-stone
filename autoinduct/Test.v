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

Inductive list (T : Type) : Type :=
  | nil : list T
  | cons : T -> list T -> list T.

Fixpoint map (A B : Type) (f : A -> B) (l : list A) : list B :=
  match l with
  | @nil _ => nil _
  | @cons _ a t => @cons B (f a) (map A B f t)
  end.

Fixpoint app (A : Type) (l1 l2 : list A) : list A :=
  match l1 with
  | @nil _ => l2
  | @cons _ a t1 => @cons _ a (@app A t1 l2) 
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

Lemma map_last_sym :
  forall (A B : Type) (f : A -> B) (a : A) (l : list A),
    @app _ (@map A B f l) (@cons _ (f a) (@nil _)) = map _ _ f (@app A l (@cons _ a (@nil _))).
Proof.
  intros.
  autoinduct on (@map A B f l) || (idtac "step0 test7 fails"; induction l).
  all: (simpl; congruence).
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

Lemma map_last_sym :
  forall (A B : Type) (f : A -> B) (a : A) (l : list A),
    @app _ (@map A B f l) (@cons _ (f a) (@nil _)) = @map _ _ f (@app A l (@cons _ a (@nil _))).
Proof.
  intros.
  autoinduct on map || (idtac "step1 test7 fails"; induction l).
  all: (simpl; congruence).
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

Lemma map_last_sym :
  forall (A B : Type) (f : A -> B) (a : A) (l : list A),
    @app _ (@map A B f l) (@cons _ (f a) (@nil _)) = @map _ _ f (@app A l (@cons _ a (@nil _))).
Proof.
  intros.
  autoinduct || (idtac "step2 test7 fails"; induction l).
  all: (simpl; congruence) || (idtac "step2 test7 autoinduct runs, but chooses argument that doesn't finish this proof"; admit).
Admitted.

End Step2.