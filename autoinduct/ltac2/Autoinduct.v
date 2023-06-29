Require Import Ltac2.Ltac2.

(* stdlib fail does enter so has type unit (indeed it doesn't fail if
   there are no focused goals) *)
Ltac2 fail s := Control.backtrack_tactic_failure s.

(* If you don't want to use Unsafe.kind, but can only handle fixpoints with 2 arguments *)
Ltac2 naive_struct_arg f :=
  lazy_match! f with
  (* `fix f n m {struct n} := bla` and `fix f n {struct n} := fun m => bla` are the same thing so this handles both arity 1 and arity 2 when the first argument is the structural argument *)
  | (fix f n {struct n} := _) => 0
  | (fix f n m {struct m} := _) => 1
  end.

Ltac2 rec struct_arg f :=
  match Constr.Unsafe.kind f with
  | Constr.Unsafe.Fix structs which _ _ => Array.get structs which
  | Constr.Unsafe.Lambda _ body => Int.add 1 (struct_arg body)
  | _ => fail "not a fixpoint"
  end.

Ltac2 find_applied f :=
  match! goal with
  | [ |- context [ ?t ] ] =>
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.App g args =>
          let farg :=
            match f with
            | Some (f,farg) =>
                if Constr.equal f g then farg
                else fail "applies a different function"
            | None =>
                if Constr.is_const g then struct_arg (eval red in $g)
                else fail "not a constant"
            end
          in
          if Int.le farg (Array.length args)
          then Array.get args farg
          else fail "not applied enough"
      | _ => fail "not an application"
      end
  end.

Ltac2 autoinduct0 f :=
  let arg :=
    match f with
    | None => find_applied None
    | Some f =>
        match Constr.Unsafe.kind f with
        | Constr.Unsafe.App f args =>
            Array.get args (struct_arg (eval red in $f))
        | _ => find_applied (Some (f, struct_arg (eval red in $f)))
        end
    end
  in
  induction $arg.

Ltac2 Notation "autoinduct" "on" f(constr) := (autoinduct0 (Some f)).

Ltac2 Notation "autoinduct" := (autoinduct0 None).

(* called from Ltac2 (ltac2 doesn't expose congruence so go through ltac1 for it) *)
Goal forall n, n + 0 = n.
  intros.
  Succeed (autoinduct;simpl;ltac1:(congruence)).
  autoinduct on Nat.add;simpl;ltac1:(congruence).
Qed.

Require Import List.

Goal forall n, n + 0 = n.
Proof.
  intros.
  autoinduct on (n + 0);simpl;ltac1:(congruence).
Qed.

Goal forall l : list nat, l ++ nil = l.
Proof.
  intros.
  autoinduct on app;simpl;ltac1:(congruence).
Qed.
(* called from ltac1 *)

Ltac autoinduct :=
  ltac2:(f |-
    let f :=
      Option.get (Ltac1.to_constr f)
    in
    autoinduct0 (Some f)).

Tactic Notation "autoinduct" "on" constr(x) := autoinduct x.
Tactic Notation "autoinduct" := ltac2:(autoinduct0 None).

Set Default Proof Mode "Classic".

Goal forall n, n + 0 = n.
  intros.
  autoinduct on Nat.add;simpl;congruence.
Qed.
