From elpi Require Import elpi.

(** Contrary to the Ltac version, the difficult part in the elpi implementation
is not constructing the term but to articulate the tactics 
together. *)

Ltac myassert u :=
  let H := fresh in assert (H := u); simpl in H.

Ltac myclear H := clear H.

Elpi Tactic eliminate_ho_eq.

Elpi Accumulate lp:{{

  pred get-head i:term o:term.
    get-head (app [F|_]) R :- get-head F R.
    get-head T T.

  pred find-pos-in-context i: goal-ctx, i: term, i: int, o: int.
      find-pos-in-context [(decl T' _ _)| _XS] T N N :- coq.unify-eq T' T ok. 
      find-pos-in-context [(decl _T' _ _)| XS] T N R :- !, M is N + 1, find-pos-in-context XS T M R.
      find-pos-in-context [(def T' _ _ _) | _XS] T N N :- coq.unify-eq T' T ok. 
      find-pos-in-context [(def _T' _ _ _)| XS] T N R :- !, M is N + 1, find-pos-in-context XS T M R.
      find-pos-in-context [] _ _ _ :- coq.error "no term equal to this one in the context".

  pred clear-with-pos i: int, i: goal, o: list sealed-goal.
      clear-with-pos N ((goal Ctx _ _ _ _) as G) GL :-
        std.nth N Ctx (decl X _ _), coq.ltac.call "myclear" [trm X] G GL.
      clear-with-pos N ((goal Ctx _ _ _ _) as G) GL :-
        std.nth N Ctx (def X _ _ _), coq.ltac.call "myclear" [trm X] G GL.
      clear-with-pos _ _ _ :- coq.error "nothing to clear".
    
  pred mk-proof-eq i: term i: term, i: term, i: term, o: term.
    mk-proof-eq H T1 T2 (prod Na Ty F1) (fun Na Ty F2) :- 
      pi x\ decl x Na Ty => mk-proof-eq H (app [T1, x]) (app [T2, x]) (F1 x) (F2 x).
    mk-proof-eq H T1 T2 Codom
      (app [{{@eq_ind_r}}, Ty', T2', (fun _ Ty' (y\ (app [{{ @eq }} , Codom, app [y | L'], T2]))), app [{{@eq_refl}}, Ty, T2], T1', H]) :-
      get-head T1 T1', get-head T2 T2', coq.typecheck T1 Ty ok, coq.typecheck T1' Ty' ok,  names L, std.filter L (x\ occurs x T1) L'.

  solve ((goal Ctx _ _ _ [trm H]) as Goal) NewGoals :- std.do!
    [coq.typecheck H (app [{{ @eq }}, Ty, T1, T2]) ok, 
     mk-proof-eq H T1 T2 Ty R1, 
     find-pos-in-context Ctx H 0 N,
     coq.ltac.call "myassert" [trm R1] Goal [NewGoal| _],
     coq.ltac.open (clear-with-pos (N + 1)) NewGoal NewGoals]. 
}}.
Elpi Typecheck.

Tactic Notation "eliminate_ho_eq" constr(t) :=
  elpi eliminate_ho_eq ltac_term:(t).

Section Tests.

Variable (f : forall (A B : Type) (a : A) (b : B), A * B).
Variable (g : forall (A B : Type) (a : A) (b : B), A * B).
Variable (Heq : f = g).

Goal False. 
assert (H : length =
fun A : Type =>
fix length (l : list A) : nat :=
  match l with
  | nil => 0
  | (_ :: l')%list => S (length l')
  end) by reflexivity. eliminate_ho_eq H.
assert (H1 : Nat.add =
fix add (n m : nat) {struct n} : nat :=
  match n with
  | 0 => m
  | S p => S (add p m)
  end) by reflexivity. eliminate_ho_eq H1.
generalize Heq. intro Heq'. (* here, we have to generalize the section variable, as section variables do not appear 
in the reified context of a Coq Goal in elpi. Otherwise, the call to clear will fail *)
eliminate_ho_eq Heq'. 
Abort.

End Tests.