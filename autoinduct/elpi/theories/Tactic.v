From elpi Require Import elpi.

(* For some reasons, Coq's builtin tactics cannot be called by their
   "name" directly, unless you alias them as we do in the following line *)
Ltac coq_builtin_induction l := induction l.


(******************************************************************)
(* Here we implement "autoinduct on (f x y)" *)

(* This command begins the definition of a tactic *)
Elpi Tactic autoinduct.

(* This command puts some elpi code in the "autoinduct" tactic.

   The delimiters "lp:{{" and "}}" are used to inject elpi code in the
   middle of a Coq file. You need Visual Studio Code or CoqIDE to
   strep trough this file interactively.
*)
Elpi Accumulate lp:{{
  
  % This function takes in unput a term, the body of a recursive function,
  % and outputs an integer standing for the position of the recursive argument
  %
  % This is the signature of the function where "i:" stands for input,
  % and "o:" stands for output.
  pred index-of-struct-argument i:term, o:int.
  %
  % The function is made of two rules, one fires whenever the body is
  % an immediate fix. Eg
  %   Definition plus := fix plus n m {struct n} := ... end.
  % The fix term constructor contains the number of the recursive argument
  index-of-struct-argument (fix _ N _ _) N.
  %
  % This other rule is for recursive functions that take extra arguments, eg
  %   Definition map :=
  %     fun A B (f : A -> B) => fix map (l : list A) {struct l} := ... end.
  % In this case we *cross the binder*, make a recursive call, and
  % increment the result by one.
  %
  % Coq terms are represented in HOAS, hence in "(fun Name Ty Bo)"
  % the subterm "Bo" is a function binding the argument. If we pass
  % a term "t" to it, we obtain the body where the bound variable is
  % replaced by "t".
  index-of-struct-argument (fun _ _ F) N1 :-
    pi x\ % this crafts a fresh name x,
      index-of-struct-argument (F x) N, % get the body and recurse
    N1 is N + 1.
  % the fix term constructor contains the

  % The entry point of tactics is called "solve", it maps a goal
  % to a list of subgoals. A goal is a tuple gathering the proof context
  % and the statement to prove, among other things. The last element of
  % the tuple is that list of arguments passed to the tactic. Here a
  % term consisting in the application of a constant F to a list of
  % arguments Xs.
  solve (goal _ _ _ _ [trm (app [global (const F)|Xs])] as Goal) NewGoals :- !,
    % "std.assert! P Msg" is a idion in elpi: it runs P and if it fails
    % it aborts the execution printing Msg.
    %
    % Here we assert that F has a body Bo (axioms for example don't)
    std.assert! (coq.env.const-body F (some Bo)) "function is a variable/axiom",
    % Then we compute the index of the recursive argument
    std.assert! (index-of-struct-argument Bo N) "function is not a fixpoint",
    % we then extract the nth argument from Xs
    std.assert! (std.nth N Xs RecArg) "not enough arguments",
    % finally we pass the ball to Coq's builtin induction tactic
    coq.ltac.call "coq_builtin_induction" [trm RecArg] Goal NewGoals.
}}.

(* Ask elpi to typcheck the code of the current tactic *)
Elpi Typecheck.


(* Here we attach an ltac1 concrete syntax to the elpi code above *)
Tactic Notation "autoinduct" "on" constr(t) :=
  elpi autoinduct ltac_term:(t).

(* We are now ready to try our tactic! *)

(* Mini test *)
Goal forall n m : nat, n + 0 = n.
intros. now autoinduct on (n + 0).
Qed.

(******************************************************************)
(* The next step is to support "autoinduct on f" *)

(* We add more code to the same tactic, in particular a new rule
   for solve. In this case the argument is not an application, but
   just a constant *)
Elpi Accumulate lp:{{
  % autoinduct on f
  solve (goal _ _ G _ [trm (global (const C) as F)] as Goal) NewGoals :- !, std.do! [
    std.assert! (coq.env.const-body C (some Bo)) "function is a variable",
    std.assert! (index-of-struct-argument Bo N) "function is not a fixpoint",

    (pi xs l\ fold-map (app [F|xs]) l _ [xs|l]) => fold-map G [] _ RL,
    std.rev {std.map RL (xs\ t\ std.nth N xs t)} L,
    std.assert! (not (L = [])) "no occurrence of the function found in goal",
    std.map L (t\ tac\ tac = coq.ltac.open (coq.ltac.call "coq_builtin_induction" [trm t])) Tactics,
    coq.ltac.or Tactics (seal Goal) NewGoals
  ].
}}.


(******************************************************************)
(* The last step is to support "autoinduct" *) 
Elpi Accumulate lp:{{

pred find-all-induction-candidates i:term, o:list term.
  find-all-induction-candidates G Ts :-
    (pi c xs l x\ fold-map (app [global (const c)|xs]) l _ [x|l] :- sigma bo n\
      coq.env.const-body c (some bo),
      index-of-struct-argument bo n,
      std.nth n xs x) => fold-map G [] _ Ts.

  % autoinduct
  solve (goal _ _ G _ [] as Goal) NewGoals :- 
    std.map {std.rev {find-all-induction-candidates G} } (t\ tac\
      tac = coq.ltac.open (coq.ltac.call "coq_builtin_induction" [trm t]))
    Tactics,
    coq.ltac.or Tactics (seal Goal) NewGoals.
}}.

Elpi Typecheck.

Tactic Notation "autoinduct" := elpi autoinduct.
