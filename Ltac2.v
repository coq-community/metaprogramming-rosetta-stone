Require Import Ltac2.Ltac2.

Ltac2 find_applied f :=
  match! goal with
  | [ |- context [ ?t ] ] =>
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.App g args =>
          let f :=
            match f with
            | Some f =>
                if Constr.equal f g then
                  f
                else
                  Control.backtrack_tactic_failure "applies a different function"
            | None =>
                if Constr.is_const g then g
                else Control.backtrack_tactic_failure "not a constant"
            end
          in
          let f := eval red in $f in
          (f, args)
      | _ => Control.backtrack_tactic_failure "not an application"
      end
  end.

(* might want to call this in find_reducible_apply so match goal will backtrack *)
Ltac2 struct_arg f :=
  match Constr.Unsafe.kind f with
  | Constr.Unsafe.Fix structs which _ _ => Array.get structs which
  | _ => Control.backtrack_tactic_failure "not a fixpoint"
  end.

Ltac2 autoinduct0 f :=
  let (g, args) := find_applied f in
  let main_arg := Array.get args (struct_arg g) in
  induction $main_arg.

Ltac2 Notation "autoinduct" f(constr) := (autoinduct0 (Some f)).

Ltac2 Notation "autoinduct" := (autoinduct0 None).

Goal forall n, n + 0 = n.
  intros.
  Succeed (autoinduct;simpl;ltac1:(congruence)).
  autoinduct Nat.add;simpl;ltac1:(congruence).
Qed.
