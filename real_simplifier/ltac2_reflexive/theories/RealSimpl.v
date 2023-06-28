(** * Reflexive tactic to compute real expressions using Q arithmetic *)

(** This is similar to field_simplify, but
    - it handles min and max
    - it is easier to extend with additional functions which are computable in Q (like modulus)
    - it does not change the term structure except for computation (which can be an advantage or disadvantage)
    - it does not simplify a^b, because b is in nat, so one would need a nat/Z simplifier in addition

    A few notes:
    - this is a reflexive tactic, which means the relevant context (a ℝ term) is converted to a gallina data structure and the
      majority of the work (the simplification and computation) is done by gallina functions
    - the advantage of reflexive tatics is that one can prove upfront that the transformations done by gallina functions are correct
    - in this case this means the equality of the original and simplified term is proven by application of a generic lemma
    - this is much faster than constructing and type checking equality lemmas for individual cases
    - reflexive tactics typically have these components:
      - a reification tactic which converts the relevant contet to an AST in gallina
      - an interpretation tactic which converts the AST back to the original term (the inverse of reification)
      - some processing function on the AST (written in gallina)
      - a proof that the processing function has certain properties (in this case preserves equality in ℝ of the intepretation of the AST)
      - a wrapper tactic, which does the reification, posts the above proof, computes in the type of the proof and applies this in some form
    - this specific instance of a reflexive tactic takes a short cut:
      - terms which are not "understood" by the tactic, say variables or unknown functions are copied literally
      - not converting the handled terms fully to an AST type and relying on computation with explicit delta lists is "quick and dirty" but quite effective
      - the correctness proofs tend to be substantially more complicated if some form of context management is required
      - the down side of this method is that if the user supplied term or context does contain symbold of the domain the tactic computes in (ℚ, ℤ, pos in this case)
        the terms can blow up
      - to avoid this one option is to copy the Q, Z and Pos functions used and use these copies (assuming that these copies do not occur in the user supplied term)
    
    Caveats:
    - this tactic does ℚ, ℤ and Pos computation on parts of the supplied term
    - if the term includes computations with variables in these domains, the term might explode
*)

Require Import Reals.
Require Import ZArith.
Require Import QArith.
Require Import Lra.
Require Import Lia.
Require Import Ltac2.Ltac2.
Require Import Ltac2.Printf.
Require Import Ltac2.Bool.

(** ** Definition of the AST *)

Inductive Expr_UnaryOp :=
  | EU_Opp
  | EU_Inv
.

Inductive Expr_BinaryOp :=
  | EB_Add
  | EB_Sub
  | EB_Mul
  | EB_Div
  | EB_Max
  | EB_Min
.

Inductive ExprReal : Set :=
  | ER_Q      : Q -> ExprReal (* This is used for everything we can evaluate *)
  | ER_R      : R -> ExprReal (* This is used for everything we cannot evaluate *)
  | ER_Z      : Z -> ExprReal (* We could use Q for Z, but then interpretation would not be an inverse of reification *)
  | ER_Unary  : Expr_UnaryOp -> ExprReal -> ExprReal
  | ER_Binary : Expr_BinaryOp -> ExprReal -> ExprReal -> ExprReal
.

(** ** Interpretation and simplification functions *)

(** Return the ℝ function corresponding to an unary operator *)

Definition unary_fun (f : Expr_UnaryOp) : R->R :=
  match f with
  | EU_Opp => Ropp
  | EU_Inv => Rinv
  end.

(** Return the ℝ function corresponding to a binary operator *)

Definition binary_fun (f : Expr_BinaryOp) : R->R->R :=
  match f with
  | EB_Add => Rplus
  | EB_Sub => Rminus
  | EB_Mul => Rmult
  | EB_Div => Rdiv
  | EB_Max => Rmax
  | EB_Min => Rmin
  end.

(** Return the ℚ function corresponding to an unary operator *)

Definition unary_fun_q (f : Expr_UnaryOp) : Q->Q :=
  match f with
  | EU_Opp => Qopp
  | EU_Inv => Qinv
  end.

(** Return the ℚ function corresponding to a binary operator *)

Definition binary_fun_q (f : Expr_BinaryOp) : Q->Q->Q :=
  match f with
  | EB_Add => Qplus
  | EB_Sub => Qminus
  | EB_Mul => Qmult
  | EB_Div => Qdiv
  | EB_Max => Qminmax.Qmax
  | EB_Min => Qminmax.Qmin
  end.

(** Check if the argument of an unary operator is valid (that is not inversion of 0) *)

Definition unary_check_args (f : Expr_UnaryOp) (a : Q) : bool :=
  match f with
  | EU_Inv => negb ((Qnum a) =? 0)%Z
  | _ => true
  end.

(** Check if the arguments of a binary operator are valid (that is not division by 0) *)

Definition binary_check_args (f : Expr_BinaryOp) (a b : Q) : bool :=
  match f with
  | EB_Div => negb ((Qnum b) =? 0)%Z
  | _ => true
  end.

(** Interpret an AST, that is convert it back to a ℝ term - this function and the reification tactic must be inverse *)

Fixpoint interpret (e : ExprReal) : R :=
  match e with
  | ER_Q q => Q2R q
  | ER_R r => r
  | ER_Z z => IZR z
  | ER_Unary f a => (unary_fun f) (interpret a)
  | ER_Binary f a b => (binary_fun f) (interpret a) (interpret b)
  end.

(** Simplify an AST by computation using ℚ arithmetic *)

Fixpoint simplify (e : ExprReal) : ExprReal :=
  match e with
  | ER_Q q => ER_Q q
  | ER_R r => ER_R r
  | ER_Z z => ER_Q (z#1)
  | ER_Unary f a =>
    let a':=simplify a in
    match a' with
    | ER_Q aq =>
      if unary_check_args f aq
      then ER_Q ((unary_fun_q f) aq)
      else ER_Unary f a'
    | _ => ER_Unary f a'
    end
  | ER_Binary f a b =>
    let a':=simplify a in
    let b':=simplify b in
    match a', b' with
    | ER_Q aq, ER_Q bq =>
      if binary_check_args f aq bq
      then ER_Q ((binary_fun_q f) aq bq)
      else ER_Binary f a' b'
    | _, _ => ER_Binary f a' b'
    end
  end.

(** Convert resulting "Q2R (n#d)" terms to quotients of integers in ℝ - or an integer if the denominator is 1 *)

(* ToDo: do reduction of Q as well *)

Fixpoint cleanup (e : ExprReal) : ExprReal :=
  match e with
  | ER_Q (z # 1) => ER_Z z
  | ER_Q (n # d) => ER_Binary EB_Div (ER_Z n) (ER_Z (Z.pos d))
  | ER_R r => e
  | ER_Z z => e
  | ER_Unary f a => ER_Unary f (cleanup a)
  | ER_Binary f a b => ER_Binary f (cleanup a) (cleanup b)
  end.

(** ** Proofs that the simplification and cleanup functions are correct *)

(** *** ℚ ℝ arithmetic equivalence lemmas missing in the standard library *)

Lemma Q2R_max: forall x y : Q,
  Q2R (Qminmax.Qmax x y) = Rmax (Q2R x) (Q2R y).
Proof.
  intros x y.
  destruct (Qlt_le_dec x y) as [Hlt|Hle].
  - rewrite Qminmax.Q.max_r, Rmax_right.
    + reflexivity.
    + apply Qreals.Qle_Rle, Qlt_le_weak, Hlt.
    + apply Qlt_le_weak, Hlt. (* Not sure why lra doesn't work here *)
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

(** *** Correctness lemmas *)

(** The interpretation of a term before and after cleanup is equal in ℝ *)

Lemma cleanup_correct: forall (e : ExprReal),
  interpret e = interpret (cleanup e).
Proof.
  intros e; induction e as [q|r|z|f a IHa|f a IHa b IHb].
  - (* Q *) cbn.
    destruct q as [n d]; destruct d; try reflexivity.
    unfold Q2R; cbn; ltac1:(lra).
  - (* R *) reflexivity.
  - (* Z *) reflexivity.
  - (* unary *) cbn; rewrite IHa; reflexivity.
  - (* binary *) cbn; rewrite IHa, IHb; reflexivity.
Qed.

(** The interpretation of a term before and after simplification is equal in ℝ *)

Lemma simplify_correct: forall (e : ExprReal),
  interpret e = interpret (simplify e).
Proof.
  intros e; induction e as [q|r|z|f a IHa|f a IHa b IHb].
  - (* Q *) reflexivity.
  - (* R *) reflexivity.
  - (* Z *) cbn; unfold Q2R; cbn; ltac1:(lra).
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
        ltac1:(lia).
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
        ltac1:(lia).
    + rewrite Q2R_max; reflexivity.
    + rewrite Q2R_min; reflexivity.
Qed.

(** The interpretation of a term before and after simplification and cleanup is equal in ℝ *)

Lemma cleanup_simplify_correct: forall (e : ExprReal),
  interpret e = interpret (cleanup (simplify e)).
Proof.
  intros e.
  rewrite <- cleanup_correct.
  apply simplify_correct.
Qed.

(** ** Reification and main tactic *)

(** *** Debugging *)

(** These notations are intended to wrap printf and can be defined to t() or () to enable / disable the prints.
    dbg1 is for low verbosity output, dbg2 for high verbosity output *)

Ltac2 Notation "dbg1" t(thunk(tactic(6))) := ().
Ltac2 Notation "dbg2" t(thunk(tactic(6))) := ().

(** *** Term classification *)

(** Check if "val" is a literal positive *)

Ltac2 rec is_literal_positive (val : constr) : bool :=
  lazy_match! val with
  | xI ?sub => is_literal_positive sub
  | xO ?sub => is_literal_positive sub
  | xH => true
  | _ => false
  end.

(** Check if "val" is a literal ℤ *)

Ltac2 is_literal_Z (val : constr) : bool :=
  lazy_match! val with
  | Z0 => true
  | Zpos ?pos => is_literal_positive pos
  | Zneg ?pos => is_literal_positive pos
  | _ => false
  end.

(** Check if "val" is a literal ℚ *)

Ltac2 is_literal_Q (val : constr) : bool :=
  lazy_match! val with
  | (?n # ?d)%Q => is_literal_Z n && is_literal_positive d
  | _ => false
  end.

(** *** Reification *)

(** This converts a term in ℝ to a ExprReal AST structure - this tactic and "interpret" must be inverse to each other *)

(** Note: we can't prove that the tactic and "interpret" are inverses - if they are not the tactic will fail when trying to unify the term in the goal with the interpreted AST.
    Probably if the reification would be done in MetaCoq, one could prove this. *)

Ltac2 rec reify_ExprReal (e : constr) : constr :=
  (dbg2 printf "=> reify_ExprReal %t" e);
  let res := lazy_match! e with
  | IZR ?z      => if is_literal_Z z then '(ER_Z $z) else '(ER_R $e)
  | Q2R ?q      => if is_literal_Q q then '(ER_Q $q) else '(ER_R $e)
  | (- ?a)%R    => let a':=reify_ExprReal a in '(ER_Unary EU_Opp $a')
  | (/ ?a)%R    => let a':=reify_ExprReal a in '(ER_Unary EU_Inv $a')
  | (?a + ?b)%R => let a':=reify_ExprReal a in let b':=reify_ExprReal b in '(ER_Binary EB_Add $a' $b')
  | (?a - ?b)%R => let a':=reify_ExprReal a in let b':=reify_ExprReal b in '(ER_Binary EB_Sub $a' $b')
  | (?a * ?b)%R => let a':=reify_ExprReal a in let b':=reify_ExprReal b in '(ER_Binary EB_Mul $a' $b')
  | (?a / ?b)%R => let a':=reify_ExprReal a in let b':=reify_ExprReal b in '(ER_Binary EB_Div $a' $b')
  | Rmax ?a ?b  => let a':=reify_ExprReal a in let b':=reify_ExprReal b in '(ER_Binary EB_Max $a' $b')
  | Rmin ?a ?b  => let a':=reify_ExprReal a in let b':=reify_ExprReal b in '(ER_Binary EB_Min $a' $b')
  | ?a          => '(ER_R $a)
  end in
  (dbg2 printf "<= reify_ExprReal %t" res);
  res.

(** *** Main tactic "real_simplify" *)

(** Two tactics to create a fresh name *)

Ltac2 rec ident_list_of_hyp_list(l : (ident * constr option * constr) list) :=
  match l with
  | h :: t => let (id,val,type) := h in id :: ident_list_of_hyp_list t
  | [] => []
end.

Ltac2 fresh_name_not_in_local_hyps (base : ident) :=
  let hypids := ident_list_of_hyp_list (Control.hyps ()) in
  let fresh_name_handler := Fresh.Free.of_ids hypids in
  Fresh.fresh fresh_name_handler base.

(** Create a reduction flags structure. I am not using the "eval cbv" notation for two reasons:
    - I am not sure how to do an "eval in type of hyp" in ltac2
    - One might want to compute the delta symbol lists, e.g. all symbols in certain ℤ and ℚ modules *)

Ltac2 redflags_delta_only_all (syms : Std.reference list) :=
  {
    (* beta: expand the application of an unfolded functions by substitution *)
    Std.rBeta := true;
    (* delta: true = expand all but rConst; false = expand only rConst *)
    Std.rDelta := false;
    (* Note: iota in tactics like cbv is a shorthand for match, fix and cofix *)
    (* iota-match: simplify matches by choosing a pattern *)
    Std.rMatch := true;
    (* iota-fix: simplify fixpoint expressions by expanding one level *)
    Std.rFix := true;
    (* iota-cofix: simplify cofixpoint expressions by expanding one level *)
    Std.rCofix := true;
    (* zeta: expand let expressions by substitution *)
    Std.rZeta := true;
    (* Symbols to expand *)
    Std.rConst := syms
  }.

(** This is the list of symbols we need to reduce for interpretation, simplification and computation.
    Essentially one creates this list first by adding known symbols, trying it and adding symbols remaining in the term.
    Note: the resulting terms can be large and CoqIDE is *much* faster than VSCoq in displaying these.
*)

Ltac2 interpretation_symbols () : Std.reference list := [
  (* Simplification and Interpretation functions *)
  reference:(interpret); reference:(simplify); reference:(cleanup);
  reference:(binary_fun); reference:(unary_fun);
  reference:(binary_fun_q); reference:(unary_fun_q);
  reference:(binary_check_args); reference:(unary_check_args);
  (* Z unary, binary, comparison, min/max *)
  reference:(Qnum); reference:(Qden); reference:(Qopp); reference:(Qinv);
  reference:(Qplus); reference:(Qminus); reference:(Qmult); reference:(Qdiv);
  reference:(Qcompare);
  reference:(Qminmax.Qmax); reference:(Qminmax.Qmin); reference:(GenericMinMax.gmax); reference:(GenericMinMax.gmin);
  (* Z unary, binary, comparison, internal *)
  reference:(Z.opp);
  reference:(Z.add); reference:(Z.sub); reference:(Z.mul);
  reference:(Z.eqb); reference:(Z.compare);
  reference:(Z.pos_sub); reference:(Z.succ_double); reference:(Z.pred_double);
  (* Pos unary, binary, comparison, internal *)
  reference:(Pos.succ);
  reference:(Pos.add); reference:(Pos.sub); reference:(Pos.mul);
  reference:(Pos.compare); reference:(Pos.compare_cont);
  reference:(Pos.pred_double);
  (* Boolean *)
  reference:(negb)
].

(** The main tactic, which reifies the supplied term, poses "cleanup_simplify_correct" applied to the ast, computes in the type of this lemma and rewrites with it *)

Ltac2 real_simplify (term : constr) : unit :=
  (dbg1 printf "real_simplify: term = %t" term);
  let ast := reify_ExprReal term in
  (dbg1 printf "real_simplify: AST = %t" ast);
  let theorem_id:=fresh_name_not_in_local_hyps @__equality in
  pose ($theorem_id:=(cleanup_simplify_correct $ast));
  Std.cbv
    (redflags_delta_only_all (interpretation_symbols()))
    {Std.on_hyps:=Some [(theorem_id, Std.AllOccurrences, Std.InHypTypeOnly)]; Std.on_concl:=Std.NoOccurrences};
  let thereom:=Env.instantiate (Std.VarRef theorem_id) in
  rewrite $thereom; clear $theorem_id
  .

(** An Ltac1 wrapper for the tactic *)

Ltac real_simplify := ltac2:(term |- real_simplify (Option.get (Ltac1.to_constr term))).

(** ** Tests *)

Section Test.
Variable x : R.
Open Scope R.

Goal (x+(Rmax ((3*4+5-6)/7) (1/2)) = x + 11/7).
  match! goal with [ |- (?a = ?b) ] => real_simplify a end.
  reflexivity.
Qed.

End Test.
