(* General imports to work with TemplateMonad *)
From MetaCoq.Template Require Import All.
From MetaCoq Require Import bytestring.
Require Import List.
Import MCMonadNotation ListNotations.
Open Scope bs.

Definition autoinduct {A} (a : A) : TemplateMonad typed_term :=
  a' <- tmEval cbv a ;;
  (* get the inductive representation of a *)
  t <- tmQuote a' ;;
  (* decompose into head and arguments *)
  let (hd, args) := decompose_app t in
  match hd with
  | tFix mfix idx =>
      match nth_error mfix idx with
      | Some f => match nth_error args (f.(rarg)) with
                 | Some x => tmUnquote x
                 | None => tmFail "not enough arguments for induction"
                 end
      | None => tmFail "ill-typed fixpoint"
      end
  | _ => tmFail "passed term does not unfold to a fixpoint"
  end.

Tactic Notation "autoinduct" constr(f) :=
  run_template_program (autoinduct f)
    (* get out the term from the pair of type and term, do induction *)
    (fun x => let t := eval unfold my_projT2 in (my_projT2 x) in
             induction t).

Lemma test : forall n, n + 0 = n.
Proof.
  intros.
  autoinduct (plus n 0).
  all: cbn; congruence.
Qed.

Lemma map_length : forall [A B : Type] (f : A -> B) (l : list A), #|map f l| = #|l|.
Proof.
  intros. autoinduct (map f l); simpl; auto.
Qed.
