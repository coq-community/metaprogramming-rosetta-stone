Require Import Ltac2.Ltac2.

Ltac2 find_reducible_apply () :=
  match! goal with
  | [ |- context [ ?f ] ] =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.App f args =>
          (* this requires a patch to coq to backtrack if f is not reducible *)
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

Ltac2 autoinduct () :=
  let (f, args) := find_reducible_apply () in
  let main_arg := Array.get args (struct_arg f) in
  induction $main_arg.

Ltac2 Notation "autoinduct" := (autoinduct()).

Goal forall n, n + 0 = n.
  intros.
  autoinduct ;simpl;ltac1:(congruence).
Qed.
