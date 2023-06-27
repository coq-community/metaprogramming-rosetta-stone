Require Import Ltac2.Ltac2.

Ltac2 find_applied f :=
  match! goal with
  | [ |- context [ ?t ] ] =>
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.App g args =>
          if Constr.equal f g then
            let g := eval red in $g in
              (g, args)
          else
            Control.backtrack_tactic_failure "applies a different function"
      | _ => Control.backtrack_tactic_failure "not an application"
      end
  end.

(* might want to call this in find_reducible_apply so match goal will backtrack *)
Ltac2 struct_arg f :=
  match Constr.Unsafe.kind f with
  | Constr.Unsafe.Fix structs which _ _ => Array.get structs which
  | _ => Control.backtrack_tactic_failure "not a fixpoint"
  end.

Ltac2 autoinduct f :=
  let (g, args) := find_applied f in
  let main_arg := Array.get args (struct_arg g) in
  induction $main_arg.

Ltac2 Notation "autoinduct" f(constr) := (autoinduct f).

Goal forall n, n + 0 = n.
  intros.
  autoinduct Nat.add;simpl;ltac1:(congruence).
Qed.
