From elpi Require Import elpi.

Ltac induction' l := induction l.

Elpi Tactic autoinduct.
Elpi Accumulate lp:{{
  % autoinduct on (f x y)
  solve (goal _ _ _ _ [trm (app [global (const F)|Xs])] as Goal) NewGoals :- !,
    std.assert! (coq.env.const-body F (some Bo)) "function is a variable",
    std.assert! (index-of-struct-argument Bo N) "function is not a fixpoint",
    coq.ltac.call "induction'" [trm {std.nth N Xs}] Goal NewGoals.

  % autoinduct on f
  solve (goal _ _ G _ [trm (global (const C) as F)] as Goal) NewGoals :- !, std.do! [
    std.assert! (coq.env.const-body C (some Bo)) "function is a variable",
    std.assert! (index-of-struct-argument Bo N) "function is not a fixpoint",
    (pi xs l\ fold-map (app [F|xs]) l _ [xs|l]) => fold-map G [] _ RL,
    std.rev {std.map RL (xs\ t\ std.nth N xs t)} L,
    std.assert! (not (L = [])) "no occurrence of the function found in goal",
    std.map L (t\ tac\ tac = coq.ltac.open (coq.ltac.call "induction'" [trm t])) Tactics,
    coq.ltac.or Tactics (seal Goal) NewGoals
  ].

  % autoinduct
  solve (goal _ _ G _ [] as Goal) NewGoals :- 
    std.map {std.rev {find-all-induction-candidates G} } (t\ tac\
      tac = coq.ltac.open (coq.ltac.call "induction'" [trm t]))
    Tactics,
    coq.ltac.or Tactics (seal Goal) NewGoals.

  pred index-of-struct-argument i:term, o:int.
  index-of-struct-argument (fix _ N _ _) N.
  index-of-struct-argument (fun _ _ F) N1 :-
    pi x\ index-of-struct-argument (F x) N,
    N1 is N + 1.

  pred find-all-induction-candidates i:term, o:list term.
  find-all-induction-candidates G Ts :-
    (pi c xs l x\ fold-map (app [global (const c)|xs]) l _ [x|l] :- sigma bo n\
      coq.env.const-body c (some bo),
      index-of-struct-argument bo n,
      std.nth n xs x) => fold-map G [] _ Ts.
}}.
Elpi Typecheck.

Tactic Notation "autoinduct" "on" constr(t) :=
  elpi autoinduct ltac_term:(t).

Tactic Notation "autoinduct" := elpi autoinduct.