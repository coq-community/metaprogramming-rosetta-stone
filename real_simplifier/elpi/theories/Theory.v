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

Inductive ExprReal : Set :=
  | ER_Q      : Q -> ExprReal
  | ER_R      : R -> ExprReal
  | ER_Z      : Z -> ExprReal
  | ER_Unary  : Expr_UnaryOp -> ExprReal -> ExprReal
  | ER_Binary : Expr_BinaryOp -> ExprReal -> ExprReal -> ExprReal.
    
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

Fixpoint interpret (e : ExprReal) : R :=
  match e with
  | ER_Q q => Q2R q
  | ER_R r => r
  | ER_Z z => IZR z
  | ER_Unary f a => (unary_fun f) (interpret a)
  | ER_Binary f a b => (binary_fun f) (interpret a) (interpret b)
  end.

Fixpoint simplify (e : ExprReal) : ExprReal :=
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
  end.

Fixpoint cleanup (e : ExprReal) : ExprReal :=
  match e with
  | ER_Q (z # 1) => ER_Z z
  | ER_Q (n # d) => ER_Binary EB_Div (ER_Z n) (ER_Z (Z.pos d))
  | ER_R r => e
  | ER_Z z => e
  | ER_Unary f a => ER_Unary f (cleanup a)
  | ER_Binary f a b => ER_Binary f (cleanup a) (cleanup b)
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

Lemma cleanup_correct: forall (e : ExprReal),
  interpret e = interpret (cleanup e).
Proof.
  intros e; induction e as [q|r|z|f a IHa|f a IHa b IHb].
  - (* Q *) cbn.
    destruct q as [n d]; destruct d; try reflexivity.
    unfold Q2R; cbn; lra.
  - (* R *) reflexivity.
  - (* Z *) reflexivity.
  - (* unary *) cbn; rewrite IHa; reflexivity.
  - (* binary *) cbn; rewrite IHa, IHb; reflexivity.
Qed.

Lemma simplify_correct: forall (e : ExprReal),
  interpret e = interpret (simplify e).
Proof.
  intros e; induction e as [q|r|z|f a IHa|f a IHa b IHb].
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
    destruct (simplify a) as [qa| | | |]; rewrite IHa;
    destruct (simplify b) as [qb| | | |]; rewrite IHb; try reflexivity.
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
Qed.

Lemma cleanup_simplify_correct: forall (e : ExprReal),
  interpret e = interpret (cleanup (simplify e)).
Proof.
  intros e.
  rewrite <- cleanup_correct.
  apply simplify_correct.
Qed.
