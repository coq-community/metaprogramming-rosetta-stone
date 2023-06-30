From Coq Require Import ZArith.

(* ncons n x s = x :: ... :: x :: s where x is repeated for n times *)
Fixpoint ncons {T : Type} (n : nat) (x : T) (s : list T) : list T :=
  match n with
  | S n' => cons x (ncons n' x s)
  | 0 => s
  end.

(* reified additive group expressions *)
Inductive AGExpr : Set :=
  | AGX : nat -> AGExpr                 (* variable *)
  | AGO : AGExpr                        (* zero     *)
  | AGOpp : AGExpr -> AGExpr            (* opposite *)
  | AGAdd : AGExpr -> AGExpr -> AGExpr. (* addition *)

(* normalizing a reified term to a formal sum, assuming the commutativity of  *)
(* addition                                                                   *)
Fixpoint ZMnorm (e : AGExpr) : list Z :=
  match e with
  | AGX j => ncons j 0%Z (cons 1%Z nil)
  | AGO => nil
  | AGOpp e1 => List.map Z.opp (ZMnorm e1)
  | AGAdd e1 e2 =>
    (fix add_rec (xs ys : list Z) : list Z :=
       match xs, ys with
       | nil, s | s, nil => s
       | cons x xs, cons y ys => cons (Z.add x y) (add_rec xs ys)
       end) (ZMnorm e1) (ZMnorm e2)
  end.

Section AGeval.

(* We assume the carrier type and the additive group operators on it as       *)
(* section variables.                                                         *)
Context {G : Type} (zeroG : G) (oppG : G -> G) (addG : G -> G -> G).

(* the interpretation function for AGExpr *)
Fixpoint AGeval (vm : list G) (e : AGExpr) : G :=
  match e with
  | AGX j => List.nth j vm zeroG
  | AGO => zeroG
  | AGOpp e1 => oppG (AGeval vm e1)
  | AGAdd e1 e2 => addG (AGeval vm e1) (AGeval vm e2)
  end.

(* multiplication of a group element by a binary integer *)
Definition mulGz (x : G) (n : Z) : G :=
  match n with
  | Z0 => zeroG
  | Zpos p => Pos.iter (fun y => addG y x) zeroG p
  | Zneg p => oppG (Pos.iter (fun y => addG y x) zeroG p)
  end.

(* the interpretation function for formal sums *)
Fixpoint ZMsubst (vm : list G) (e : list Z) {struct e} : G :=
  match e, vm with
  | cons n e', cons x vm' => addG (mulGz x n) (ZMsubst vm' e')
  | _, _ => zeroG
  end.

(* an auxiliary function for the Z-module simplifier *)
Fixpoint ZMsimpl_aux (vm : list G) (e : list Z) {struct e} : list G * list G :=
  match e, vm with
  | cons Z0 e', cons _ vm' => ZMsimpl_aux vm' e'
  | cons (Z.pos p) e', cons x vm' =>
    let '(e1, e2) := ZMsimpl_aux vm' e' in (Pos.iter (cons x) e1 p, e2)
  | cons (Z.neg p) e', cons x vm' =>
    let '(e1, e2) := ZMsimpl_aux vm' e' in (e1, Pos.iter (cons x) e2 p)
  | _, _ => (nil, nil)
  end.

(* We assume the commutative group axioms on G and its operators as section   *)
(* variables.                                                                 *)
Context (addA : forall x y z : G, addG x (addG y z) = addG (addG x y) z).
Context (addC : forall x y : G, addG x y = addG y x).
Context (add0x : forall x : G, addG zeroG x = x).
Context (addNx : forall x : G, addG (oppG x) x = zeroG).

(* some facts about the commutative group structure *)
Let addx0 x : addG x zeroG = x.
Proof. now rewrite addC, add0x. Qed.

Let addxN x : addG x (oppG x) = zeroG.
Proof. now rewrite addC, addNx. Qed.

Let oppK x : oppG (oppG x) = x.
Proof.
now rewrite <- (add0x (oppG (oppG x))), addC, <- (addNx x), addA, addNx, add0x.
Qed.

Let oppD x y : oppG (addG x y) = addG (oppG x) (oppG y).
Proof.
rewrite <- (add0x (addG (oppG x) _)), <- (addNx (addG y x)), <- addA.
replace (addG (addG y x) (addG (oppG x) (oppG y))) with zeroG.
  now rewrite addx0, addC.
now rewrite addA, <- (addA y), addxN, addx0, addxN.
Qed.

Let oppB x y : oppG (addG x (oppG y)) = addG y (oppG x).
Proof. now rewrite oppD, oppK. Qed.

Let opp0 : oppG zeroG = zeroG.
Proof. now rewrite <- (add0x (oppG _)), addxN. Qed.

Let addCA x y z : addG x (addG y z) = addG y (addG x z).
Proof. now rewrite !addA, (addC x). Qed.

Let addAC x y z : addG (addG x y) z = addG (addG x z) y.
Proof. now rewrite <- !addA, (addC y). Qed.

Let addACA x y z t : addG (addG x y) (addG z t) = addG (addG x z) (addG y t).
Proof. now rewrite !addA; f_equal; rewrite <- !addA; f_equal; rewrite addC. Qed.

Let mulzDl x n m : mulGz x (Z.add n m) = addG (mulGz x n) (mulGz x m).
Proof.
assert (Hpos : forall p q,
  addG (mulGz x (Z.pos p)) (mulGz x (Z.pos q)) = mulGz x (Z.pos (Pos.add p q))).
  intros p q; simpl; rewrite !Pos2Nat.inj_iter, Pos2Nat.inj_add.
  induction (Pos.to_nat p) as [|p' IHp']; simpl; trivial.
  now rewrite addAC, IHp'.
assert (Hneg : forall p q,
  addG (mulGz x (Z.pos p)) (mulGz x (Z.neg q)) = mulGz x (Z.pos p - Z.pos q)).
{
  intros p q; change (mulGz x (Z.neg q)) with (oppG (mulGz x (Z.pos q))).
  destruct (Pos.compare_spec q p) as [q_eq_p|q_lt_p|p_lt_q].
  - now rewrite q_eq_p, addxN, Z.sub_diag.
  - rewrite <- (Pos2Z.inj_sub _ _ q_lt_p), <- (addx0 (mulGz x (Z.pos (p - q)))).
    rewrite <- (addxN (mulGz x (Z.pos q))), addA; f_equal.
    now rewrite Hpos, Pos.sub_add.
  - rewrite <- (Z.opp_involutive (_ - _)), Z.opp_sub_distr, Z.add_comm.
    rewrite Z.add_opp_r, <- (Pos2Z.inj_sub _ _ p_lt_q).
    change (mulGz x (- Z.pos (q - p))) with (oppG (mulGz x (Z.pos (q - p)))).
    rewrite <- (add0x (oppG (mulGz x (Z.pos (q - p))))).
    rewrite <- (addxN (mulGz x (Z.pos p))), <- addA; f_equal.
    now rewrite <- oppD, Hpos, Pplus_minus; [| apply Pos.lt_gt].
}
destruct n as [|n|n], m as [|m|m]; rewrite ?add0x, ?addx0; trivial.
- now rewrite Hpos.
- now rewrite Hneg.
- now rewrite addC, Hneg.
- change (mulGz x (Z.neg n + Z.neg m)) with (oppG (mulGz x (Z.pos (n + m)))).
  now rewrite <- Hpos, oppD.
Qed.

(* the correctness lemma for normalization *)
Lemma ZM_norm_subst (vm : list G) (e : AGExpr) :
  ZMsubst vm (ZMnorm e) = AGeval vm e.
Proof.
induction e as [j| |e IHe|e1 IHe1 e2 IHe2]; simpl; trivial.
- revert vm; induction j as [|j IHj]; destruct vm as [|v vm]; simpl; trivial.
  + now rewrite add0x, addx0.
  + now rewrite add0x, IHj.
- rewrite <- IHe; clear IHe; revert vm.
  induction (ZMnorm e) as [|x xs IHxs]; destruct vm as [|v vm]; simpl;
    try now rewrite opp0.
  rewrite IHxs, oppD; f_equal.
  now destruct x; simpl; [rewrite opp0| |rewrite oppK].
- rewrite <- IHe1, <- IHe2; clear IHe1 IHe2; revert vm.
  generalize (ZMnorm e1) as xs, (ZMnorm e2) as ys; induction xs as [|x xs IHxs];
    destruct ys as [|y ys]; destruct vm as [|v vm]; simpl;
    try now (rewrite add0x || rewrite addx0).
  now rewrite addACA, <-IHxs, mulzDl.
Qed.

(* the reflection lemma for proving valid commutative group equations *)
Lemma ZM_correct (vm : list G) (e1 e2 : AGExpr) :
  let isZero (n : Z) := match n with Z0 => true | _ => false end in
  List.forallb isZero (ZMnorm (AGAdd e1 (AGOpp e2))) = true ->
  AGeval vm e1 = AGeval vm e2.
Proof.
set (e := AGAdd e1 (AGOpp e2)); intros isZero Hzeros.
rewrite <- (addx0 (AGeval vm e1)), <- (add0x (AGeval vm e2)).
rewrite <- (addNx (AGeval vm e2)), addA at 1; f_equal.
change (addG (AGeval vm e1) (oppG (AGeval vm e2))) with (AGeval vm e).
rewrite <- ZM_norm_subst; revert vm Hzeros.
induction (ZMnorm e) as [|x xs IHxs]; destruct vm as [|v vm]; simpl; trivial.
now destruct x; try discriminate; rewrite add0x; apply IHxs.
Qed.

(* the reflection lemma for simplifying commutative group equations *)
Lemma ZMsimpl_correct (vm : list G) (e1 e2 : AGExpr) :
  let sum zero add zs :=
    match zs with cons z zs => List.fold_left add zs z | nil => zero end
  in
  (forall zero add vm', zero = zeroG -> add = addG -> vm' = vm ->
   let norm := ZMnorm (AGAdd e1 (AGOpp e2)) in
   let '(xs, ys) := ZMsimpl_aux vm' norm in
   sum zero add xs = sum zero add ys) ->
  AGeval vm e1 = AGeval vm e2.
Proof.
set (e := AGAdd e1 (AGOpp e2)).
intros sum H; generalize (H _ _ _ eq_refl eq_refl eq_refl); clear H; cbv zeta.
case_eq (ZMsimpl_aux vm (ZMnorm e)); intros xs ys simplE Hsum.
rewrite <- (addx0 (AGeval vm e1)), <- (add0x (AGeval vm e2)).
rewrite <- (addNx (AGeval vm e2)), addA at 1; f_equal.
change (addG (AGeval vm e1) (oppG (AGeval vm e2))) with (AGeval vm e).
rewrite <- ZM_norm_subst.
replace zeroG with (addG (sum zeroG addG xs) (oppG (sum zeroG addG ys)))
  by now rewrite Hsum; rewrite addxN.
assert (sumE : forall zs, sum zeroG addG zs = List.fold_right addG zeroG zs).
  destruct zs as [|z zs]; simpl; trivial.
  revert z; induction zs as [|z' zs IHzs]; intro z; simpl.
    now rewrite addx0.
  now rewrite IHzs, addA.
rewrite !sumE; clear sum Hsum sumE; revert vm xs ys simplE.
induction (ZMnorm e) as [|z zs IHzs]; destruct vm as [|v vm]; intros xs ys.
- now intro H; injection H; intros; subst; simpl; rewrite addxN.
- now intro H; injection H; intros; subst; simpl; rewrite addxN.
- now destruct z; intro H; injection H; intros; subst; simpl; rewrite addxN.
- destruct z as [|p|p]; simpl; [rewrite add0x; apply IHzs| |].
    generalize (IHzs vm); clear IHzs.
    destruct (ZMsimpl_aux vm zs) as [xs' ys']; intro IHzs.
    rewrite (IHzs xs' ys' eq_refl); intro H; injection H; clear H IHzs.
    intros; subst xs ys; rewrite addA, !Pos2Nat.inj_iter; f_equal.
    induction (Pos.to_nat p) as [|n IHn]; simpl; [now rewrite add0x |].
    now rewrite addAC, IHn, (addC v).
  generalize (IHzs vm); clear IHzs.
  destruct (ZMsimpl_aux vm zs) as [xs' ys']; intro IHzs.
  rewrite (IHzs xs' ys' eq_refl); intro H; injection H; clear H IHzs.
  intros; subst xs ys; rewrite addCA, <- oppD, !Pos2Nat.inj_iter.
  f_equal; f_equal.
  induction (Pos.to_nat p) as [|n IHn]; simpl; [now rewrite add0x |].
  now rewrite addAC, IHn, (addC v).
Qed.

End AGeval.

(* the reflection lemmas specialized to binary integers Z *)
Fact ZM_correct_Z (vm : list Z) (e1 e2 : AGExpr) :
  List.forallb (Z.eqb 0) (ZMnorm (AGAdd e1 (AGOpp e2))) = true ->
  AGeval Z0 Z.opp Z.add vm e1 = AGeval Z0 Z.opp Z.add vm e2.
Proof.
now apply (ZM_correct _ _ _ Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l).
Qed.

Lemma ZMsimpl_correct_Z (vm : list Z) (e1 e2 : AGExpr) :
  let sum zero add zs :=
    match zs with cons z zs => List.fold_left add zs z | nil => zero end
  in
  (forall zero add vm', zero = Z0 -> add = Z.add -> vm' = vm ->
   let norm := ZMnorm (AGAdd e1 (AGOpp e2)) in
   let '(xs, ys) := ZMsimpl_aux vm' norm in
   sum zero add xs = sum zero add ys) ->
  AGeval Z0 Z.opp Z.add vm e1 = AGeval Z0 Z.opp Z.add vm e2.
Proof.
now apply
  (ZMsimpl_correct _ _ _ Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l).
Qed.

Strategy expand [AGeval].
