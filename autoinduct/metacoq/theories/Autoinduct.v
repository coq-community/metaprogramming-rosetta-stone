(* General imports to work with TemplateMonad *)
From MetaCoq.Template Require Import All.
From MetaCoq Require Import bytestring.
Require Import List.
Import MCMonadNotation ListNotations.
Open Scope bs.

Fixpoint decompose_lam_assum (Γ : context) (t : term) : context * term :=
  match t with
  | tLambda n A B => decompose_lam_assum (Γ ,, vass n A) B
  | tLetIn na b bty b' => decompose_prod_assum (Γ ,, vdef na b bty) b'
  | _ => (Γ, t)
  end.

Definition autoinduct (p : program) : term :=
  let (Σ, t) := p in
  (* decompose into head and arguments *)
  let (hd, args) := decompose_app t in
  let (n, hd') := match hd with
             | tConst kn _ => match lookup_constant Σ kn with
                             | Some b => match b.(cst_body) with
                                        | Some b => let (lambdas, rhd) := decompose_lam_assum [] b in
                                                   (List.length lambdas, rhd)
                                        | None => (0, tVar "error: constant has no body")
                                        end
                             | None => (0, tVar "error: constant not declared")
                             end
             | x => (0, x)
             end in
  match hd' with
  | tFix mfix idx =>
      match nth_error mfix idx with
      | Some f => match nth_error args (n + f.(rarg)) with
                 | Some x => x
                 | None => tVar "not enough arguments for induction"
                 end
      | None => tVar "ill-typed fixpoint"
      end
  | _ => tVar "passed term does not unfold to a fixpoint"
  end.

Tactic Notation "autoinduct" "on" constr(f) :=
  run_template_program (t <- tmQuoteRec f ;;
                        a <- tmEval lazy (autoinduct t) ;;
                        tmUnquote a)
    (fun x => let t := eval unfold my_projT2 in (my_projT2 x) in
             induction t).


Tactic Notation "autoinduct" := fail.

Lemma test : forall n, n + 0 = n.
Proof.
  intros.
  autoinduct on (plus n 0).
  all: cbn; congruence.
Qed.

Lemma map_length : forall [A B : Type] (f : A -> B) (l : list A), #|map f l| = #|l|.
Proof.
  intros. autoinduct on (map f l); simpl; auto.
Qed.
