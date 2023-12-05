From elpi Require Import elpi.

Ltac myassert u :=
  let H := fresh in assert (H := u); simpl in H.

Elpi Tactic eliminate_ho_eq.

Elpi Accumulate lp:{{

  pred mk-proof-eq i: term i: term, i: term, i: term, i:list term, o: term.
    mk-proof-eq H T1 T2 (prod Na Ty F1) Acc (fun Na Ty F2) :- 
      pi x\ decl x Na Ty =>
        mk-proof-eq H T1 T2 (F1 x) [x|Acc] (F2 x).
    mk-proof-eq H T1 T2 _ Acc {{ @eq_ind_r _ lp:T2 lp:Predicate (eq_refl lp:T2Args) lp:T1 lp:H }} :-
      std.rev Acc Args,
      coq.mk-app T2 Args T2Args,
      Predicate = {{ fun y => lp:{{ app[ {{y}} | Args] }} = lp:T2Args }}.

  solve ((goal _ _ _ _ [trm H]) as Goal) NewGoals :- % I would recommand to look at 
    % https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_tactic.html#defining-tactics to understand the [goal] predicate

    std.do! % [std.do! L] tries to runs everything in [L] and never backtracks
    [coq.typecheck H (app [{{ @eq }}, Ty, T1, T2]) ok, % the given hypothesis should be of type [f = g] 
     mk-proof-eq H T1 T2 Ty [] R1, % we build the proof term given the initial hypothesis, the functions and their types
     coq.typecheck R1 _ ok,
     coq.ltac.call "myassert" [trm R1] Goal NewGoals].


}}.
Elpi Typecheck.


(** elpi introduces new parsing annotations for [Tactic Notation], 
here, we use [ltac_term] but we also have [ltac_term_list] 
if the tactic we defined takes several arguments *)

Tactic Notation "eliminate_ho_eq" hyp(t) :=
  elpi eliminate_ho_eq ltac_term:(t); clear t.

Section Tests.

Goal forall (f g : forall (A B : Type) (a : A) (b : B), A * B), f = g -> False.
intros f g Heq. 
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
eliminate_ho_eq Heq. 
Abort.

End Tests.







