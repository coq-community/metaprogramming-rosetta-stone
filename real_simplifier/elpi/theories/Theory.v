Require Import Reals.
Require Import ZArith.
Require Import QArith.
Require Import Lra.
Require Import Lia.

Inductive Expr_UnaryOp :=
  | EU_Opp
  | EU_Inv.

Inductive Expr_BinaryOp :=
  | EB_Add
  | EB_Sub
  | EB_Mul
  | EB_Div
  | EB_Max
  | EB_Min.

Inductive Expr_N : Set :=
  | EN_lit : nat -> Expr_N
  | EN_gen : nat -> Expr_N.

Inductive Expr_R : Set :=
  | ER_Q      : Q -> Expr_R
  | ER_R      : R -> Expr_R
  | ER_Z      : Z -> Expr_R
  | ER_Unary  : Expr_UnaryOp -> Expr_R -> Expr_R
  | ER_Binary : Expr_BinaryOp -> Expr_R -> Expr_R -> Expr_R
  | ER_Pow    : Expr_R -> Expr_N -> Expr_R.

Definition interpret_N (e : Expr_N) : nat :=
  match e with
  | EN_lit n => n
  | EN_gen n => n
  end.
    
Definition unary_fun (f : Expr_UnaryOp) : R -> R :=
  match f with
  | EU_Opp => Ropp
  | EU_Inv => Rinv
  end.

Definition binary_fun (f : Expr_BinaryOp) : R -> R -> R :=
  match f with
  | EB_Add => Rplus
  | EB_Sub => Rminus
  | EB_Mul => Rmult
  | EB_Div => Rdiv
  | EB_Max => Rmax
  | EB_Min => Rmin
  end.

Definition unary_fun_q (f : Expr_UnaryOp) : Q -> Q :=
  match f with
  | EU_Opp => Qopp
  | EU_Inv => Qinv
  end.

Definition binary_fun_q (f : Expr_BinaryOp) : Q -> Q -> Q :=
  match f with
  | EB_Add => Qplus
  | EB_Sub => Qminus
  | EB_Mul => Qmult
  | EB_Div => Qdiv
  | EB_Max => Qminmax.Qmax
  | EB_Min => Qminmax.Qmin
  end.

Definition unary_check_args (f : Expr_UnaryOp) (a : Q) : bool :=
  match f with
  | EU_Inv => negb ((Qnum a) =? 0)%Z
  | _ => true
  end.

Definition binary_check_args (f : Expr_BinaryOp) (a b : Q) : bool :=
  match f with
  | EB_Div => negb ((Qnum b) =? 0)%Z
  | _ => true
  end.

Fixpoint interpret_R (e : Expr_R) : R :=
  match e with
  | ER_Q q => Q2R q
  | ER_R r => r
  | ER_Z z => IZR z
  | ER_Unary f a => (unary_fun f) (interpret_R a)
  | ER_Binary f a b => (binary_fun f) (interpret_R a) (interpret_R b)
  | ER_Pow a b => pow (interpret_R a) (interpret_N b)
  end.

Fixpoint simplify (e : Expr_R) : Expr_R :=
  match e with
  | ER_Q q => ER_Q q
  | ER_R r => ER_R r
  | ER_Z z => ER_Q (z#1)
  | ER_Unary f a =>
    let a' := simplify a in
    match a' with
    | ER_Q aq =>
      if unary_check_args f aq
      then ER_Q ((unary_fun_q f) aq)
      else ER_Unary f a'
    | _ => ER_Unary f a'
    end
  | ER_Binary f a b =>
    let a' := simplify a in
    let b' := simplify b in
    match a', b' with
    | ER_Q aq, ER_Q bq =>
      if binary_check_args f aq bq
      then ER_Q ((binary_fun_q f) aq bq)
      else ER_Binary f a' b'
    | _, _ => ER_Binary f a' b'
    end
  | ER_Pow a b =>
    let a' := simplify a in
    match a', b with
    | ER_Q aq, EN_lit bn => ER_Q (Qpower aq (Z.of_nat bn))
    | _, _ => ER_Pow a' b
    end
  end.

Fixpoint cleanup (e : Expr_R) : Expr_R :=
  match e with
  | ER_Q (z # 1) => ER_Z z
  | ER_Q (n # d) => ER_Binary EB_Div (ER_Z n) (ER_Z (Z.pos d))
  | ER_R r => e
  | ER_Z z => e
  | ER_Unary f a => ER_Unary f (cleanup a)
  | ER_Binary f a b => ER_Binary f (cleanup a) (cleanup b)
  | ER_Pow a b => ER_Pow (cleanup a) b
  end.

Lemma Q2R_max: forall x y : Q,
  Q2R (Qminmax.Qmax x y) = Rmax (Q2R x) (Q2R y).
Proof.
  intros x y.
  destruct (Qlt_le_dec x y) as [Hlt|Hle].
  - rewrite Qminmax.Q.max_r, Rmax_right.
    + reflexivity.
    + apply Qreals.Qle_Rle, Qlt_le_weak, Hlt.
    + apply Qlt_le_weak, Hlt.
  - rewrite Qminmax.Q.max_l, Rmax_left.
    + reflexivity.
    + apply Qreals.Qle_Rle, Hle.
    + apply Hle.
Qed.

Lemma Q2R_min: forall x y : Q,
  Q2R (Qminmax.Qmin x y) = Rmin (Q2R x) (Q2R y).
Proof.
  intros x y.
  destruct (Qlt_le_dec x y) as [Hlt|Hle].
  - rewrite Qminmax.Q.min_l, Rmin_left.
    + reflexivity.
    + apply Qreals.Qle_Rle, Qlt_le_weak, Hlt.
    + apply Qlt_le_weak, Hlt.
  - rewrite Qminmax.Q.min_r, Rmin_right.
    + reflexivity.
    + apply Qreals.Qle_Rle, Hle.
    + apply Hle.
Qed.

Lemma Qpower_nat_succ: forall (x : Q) (n : nat),
  Qpower x (Z.of_nat (S n)) = x * Qpower x (Z.of_nat n).
Proof.
  intros x n.
  induction n.
  - cbn. unfold Qmult. cbn.
    rewrite Z.mul_1_r, Pos.mul_1_r.
    destruct x as [n d].
    reflexivity.
  - cbn.
    unfold Qpower_positive.
    rewrite pow_pos_succ.
    + reflexivity.
    + apply Eqsth.
    + unfold Proper, respectful; intros; subst; reflexivity.
    + intros a b c. unfold Qmult. destruct a, b, c. cbn.
      rewrite Z.mul_assoc. 
      rewrite Pos.mul_assoc.
      reflexivity.
Qed. 

Lemma Q2R_pow: forall (x : Q) (n : nat),
  (Q2R x ^ n)%R = Q2R (x ^ Z.of_nat n).
Proof.
  intros x n.
  induction n.
  - cbn. unfold Q2R. cbn. lra.
  - rewrite Qpower_nat_succ. cbn.
    rewrite Qreals.Q2R_mult.
    rewrite IHn.
    reflexivity.
Qed.

Lemma cleanup_correct: forall (e : Expr_R),
  interpret_R e = interpret_R (cleanup e).
Proof.
  intros e; induction e as [q|r|z|f a IHa|f a IHa b IHb|a IHa b].
  - (* Q *) cbn.
    destruct q as [n d]; destruct d; try reflexivity.
    unfold Q2R; cbn; lra.
  - (* R *) reflexivity.
  - (* Z *) reflexivity.
  - (* unary *) cbn; rewrite IHa; reflexivity.
  - (* binary *) cbn; rewrite IHa, IHb; reflexivity.
  - (* pow *) cbn; rewrite IHa; reflexivity.
Qed.

Lemma simplify_correct: forall (e : Expr_R),
  interpret_R e = interpret_R (simplify e).
Proof.
  intros e; induction e as [q|r|z|f a IHa|f a IHa b IHb|a IHa b].
  - (* Q *) reflexivity.
  - (* R *) reflexivity.
  - (* Z *) cbn; unfold Q2R; cbn; lra.
  - (* unary *) cbn.
    destruct (simplify a); rewrite IHa; try reflexivity.
    cbn.
    destruct f; cbn.
    + rewrite Qreals.Q2R_opp; reflexivity.
    + destruct (Z.eqb_spec (Qnum q) 0) as [Heq|Hneq]; cbn.
      * reflexivity.
      * rewrite Qreals.Q2R_inv.
        1: reflexivity.
        unfold Qeq; cbn.
        lia.
  - (* binary *) cbn.
    destruct (simplify a) as [qa| | | | |]; rewrite IHa;
    destruct (simplify b) as [qb| | | | |]; rewrite IHb; try reflexivity.
    cbn.
    destruct f; cbn.
    + rewrite Qreals.Q2R_plus; reflexivity.
    + rewrite Qreals.Q2R_minus; reflexivity.
    + rewrite Qreals.Q2R_mult; reflexivity.
    + destruct (Z.eqb_spec (Qnum qb) 0) as [Heq|Hneq]; cbn.
      * reflexivity.
      * rewrite Qreals.Q2R_div.
        1: reflexivity.
        unfold Qeq; cbn.
        lia.
    + rewrite Q2R_max; reflexivity.
    + rewrite Q2R_min; reflexivity.
  - (* Pow *) cbn.
    destruct (simplify a); rewrite IHa; try reflexivity.
    destruct b; cbn; try reflexivity.
    apply Q2R_pow.
Qed.

Lemma cleanup_simplify_correct: forall (e : Expr_R),
  interpret_R e = interpret_R (cleanup (simplify e)).
Proof.
  intros e.
  rewrite <- cleanup_correct.
  apply simplify_correct.
Qed.
