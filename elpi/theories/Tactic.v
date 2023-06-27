From elpi Require Import elpi.

Ltac induction' l := induction l.

Elpi Tactic autoinduct.
Elpi Accumulate lp:{{
  % autoinduct on (f x y)
  solve (goal _Context _RawProof _G _Proof [trm T] as Goal) NewGoals :-
    std.assert! (T = app [global (const F)|Xs]) "format",
    std.assert! (coq.env.const-body F (some Bo)) "function is a variable",
    std.assert! (find-rec-arg Bo N) "function is not a fixpoint",
    std.nth N Xs X,
    coq.ltac.call "induction'" [trm X] Goal NewGoals.
  
  pred find-rec-arg i:term, o:int.
  find-rec-arg (fix _ N _ _) N.
  find-rec-arg (fun _ _ F) N1 :-
    pi x\ find-rec-arg (F x) N,
    N1 is N + 1.
}}.
Elpi Typecheck.

Tactic Notation "autoinduct" "on" constr(t) :=
  elpi autoinduct ltac_term:(t).