From elpi Require Import elpi.

Require Import Reals.
Require Import ZArith.
Require Import QArith.

From RealSimplify Require Import Theory.
From RealSimplify.Elpi Extra Dependency "reify.elpi" as reify.
From RealSimplify.Elpi Extra Dependency "symbols.elpi" as symbols.

Elpi Tactic real_simplify.
Elpi Accumulate File reify.
Elpi Accumulate File symbols.
Elpi Accumulate lp:{{
  solve (goal _ _ G _ [] as InitialGoal) NewGoals :- std.do! [
    std.assert! (G = {{ @eq R lp:A lp:B }}) "goal is not a real equality",
    reify A RA,
    Eq = {{ cleanup_simplify_correct lp:RA }},
    coq.typecheck Eq EqT ok,
    coq.redflags.add
      coq.redflags.betaiotazeta
      {std.map {symbols} (g\ flag\ sigma C\ g = const C, flag = coq.redflags.const C)}
      RedFlags,
    @redflags! RedFlags => coq.reduction.cbv.norm EqT RedEqT,
    RedEqT = {{ lp:C = _ }},
    Proof = {{
      (@eq_rect R _ (fun t => @eq R t lp:B) _ _
        (eq_sym (lp:Eq : lp:RedEqT))
          : lp:C = lp:B)
    }},
    refine Proof InitialGoal NewGoals
  ].
}}.
Elpi Typecheck.

Tactic Notation "real_simplify" := elpi real_simplify.
