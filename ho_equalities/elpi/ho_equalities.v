From elpi Require Import elpi.

(** The main tactic [eliminate_ho_eq] takes a hypothesis which is a 
higher-order equality of the form [f = g]
and generates an proves a new hypothesis [forall x1, ... xn, f x1 ... xn = g x1 ... xn] *)

(** 
Generic considerations about the tactic:

I recommend to look first at the Ltac1 version as the comments will refer to it.
As we will see, contrary to the Ltac1 version, the difficult part in the elpi implementation
is not constructing the term but to articulate the tactics 
together. The only articulation we made here is the chaining between the 
tactic [myassert] and the tactic [myclear], and this was the longest 
part to implement.

Here, the tactic takes an hypothesis [H] of the form [f=g] and 
generates directly an inhabitant (i.e.: a proof) of [forall x1, ... xn, f x1 ... xn = g x1 ... xn]. 
Another method would have been to generate the hypothesis to prove and use a small Ltac1 or
Ltac2 script to make the proof. Articulate proof steps in elpi is difficult so I
would not recommand using a combination of elpi tactics to build a proof.
I would rather generate the terms in elpi and then go outside the elpi world and use Ltac
to prove them. 

*)

(** For some reason, elpi fails when we use original Coq tactics 
(except if they take no argument), so we have to define our own alias *)

Ltac myassert u :=
  let H := fresh in assert (H := u); simpl in H.

Ltac myclear H := clear H.


(** All elpi tactics start with these two vernacular commands: [Elpi tactic toto.] followed 
by [Elpi Accumulate lp:{{ some elpi code }}.]
We can also accumulate separate elpi files but here the code 
is small so keeping only one file is fine. 

In elpi, we use the lambda-prolog language. Every elpi program
is written as a combination of predicates, taking inputs or outputs.
For instance, [get-head T T'] takes a term [T] as input and returns a term [T'] (the same one if it is not 
an application, and its head otherwise)

Each predicate is defined by its rules.
On the left of the symbol [:-], we write the head of a rule, and on the right its premises. 
Thus, [get-head (app [F|_]) R :- get-head F R] means that the output [R] is the head of the application of [F]
to any arguments (so we use a wildcard) only if it is also the head of [F].

The good thing with elpi is that we have access to the deep syntax of Coq terms 
(contrary to Ltac1 if you remember our tedious tricks). 
The type [term], defined here: 
https://github.com/LPCIC/coq-elpi/blob/b92e2c85ecb6bb3d0eb0fbd57920d553b153e49c/elpi/coq-HOAS.elpi
represents Coq terms. You can even extend it ! 

The other very important thing is that you have quotations. In the code, you will see 
an example: [{{ @eq }}], which is simply turning the Coq term for propositional equality
into its elpi quotation. You can also use elpi antiquotation, for inserting elpi variables 
into a Coq term, but we won't need this here.

Another crucial point is that there is no such thing as a free variable in elpi. 
It uses higher-order abstact syntax: to cross a binder, we need to introduce a fresh 
variable (also called "eigenvariable") in the context of the program.
Fortunately, we have really useful elpi predicates about eigenvariables: [occurs X Y] which holds if its first 
argument [X] (a variable bound in the context) occurs in the second argument [Y], 
and [names L] which has as only argument [L] the list of all the eigenvariables introduced in the context.

Elpi has two kinds of variables: unification variables (also called "metavariables"), 
used to resolve the clauses which
define elpi predicates and written with capital letters, and eigenvariables written is small letter
(and that you have to bind explicitely as we will see).

 *)
Elpi Tactic eliminate_ho_eq.

Elpi Accumulate lp:{{
  
  % I can introduce a one-line comment with a %

  pred get-head i:term o:term. % [i:] means input and [o:] means output
    get-head (app [F|_]) R :- get-head F R.
    get-head T T.

  % This auxiliary predicate looks in the context of a goal (that is, its local definitions and hypotheses)
  % and returns the position of the term given as an input.
  % The input int here is simply an accumulator.

  pred find-pos-in-context i: goal-ctx, i: term, i: int, o: int.
      find-pos-in-context [(decl T' _ _)| _XS] T N N :- coq.unify-eq T' T ok. %coq.unify-eq returns ok when T' is syntactically equal to T
      find-pos-in-context [(decl _T' _ _)| XS] T N R :- !, M is N + 1, find-pos-in-context XS T M R.
      find-pos-in-context [(def T' _ _ _) | _XS] T N N :- coq.unify-eq T' T ok. 
      find-pos-in-context [(def _T' _ _ _)| XS] T N R :- !, M is N + 1, find-pos-in-context XS T M R.
      find-pos-in-context [] _ _ _ :- coq.error "no term equal to this one in the context".

  % This auxiliary predicate clear the Nth hypothesis of the context (the 0th is the last introduced hypothesis)
  % It uses the API coq.ltac.call in order to invoke some Ltac piece of code (here, our [myclear])
  % This calling to Ltac takes a list of arguments, the current goal and returns the list of new goals generated by the tactic.

  pred clear-with-pos i: int, i: goal, o: list sealed-goal.
      clear-with-pos N ((goal Ctx _ _ _ _) as G) GL :-
        std.nth N Ctx (decl X _ _), coq.ltac.call "myclear" [trm X] G GL.
      clear-with-pos N ((goal Ctx _ _ _ _) as G) GL :-
        std.nth N Ctx (def X _ _ _), coq.ltac.call "myclear" [trm X] G GL.
      clear-with-pos _ _ _ :- coq.error "nothing to clear".

  % Here is our main predicate, generating the proof term of forall x1, ..., xn, f x1 ... xn = g x1 ... xn
  % starting with a proof [H] of f = g, the terms f ([T1]) and g ([T2]), and their type.
  % The first rule is the recursive case: we suppose that the functions given as 
  % inputs are only partially applied (or not applied at all).
  % Consequently, we bind a eigenvariable by using [pi x\ decl x Na Ty => ...] 
  % which means that we introduce an eigenvariable variable [x] which
  % has the name [Na] and the type [Ty]. Behind the [=>], we are allowed to write some code that mentions [x].
  % So it is sufficent to make a recursive call in which we apply the functions and the resulting 
  % proof term to the variable [x].
  % The second rule is the base case. We generate the proof term which is an application of [@eq_ind_r].
  % We managed to find the exact form of the proof term by some trials and errors using Ltac's [refine].
  % Instead of focusing of its hardly readable form, I suggest that you look at the use of elpi's predicates
  % [names] and [occurs]. We needed to apply the function variable [y] on the correct arguments.
  % To find them, we looked at all the eigenvariables of our program by using [names L], and then filter these to keep 
  % only the ones in [T1] (remember that [T1] is precisely f x1 ... xn).
    
  pred mk-proof-eq i: term i: term, i: term, i: term, o: term.
    mk-proof-eq H T1 T2 (prod Na Ty F1) (fun Na Ty F2) :- 
      pi x\ decl x Na Ty => mk-proof-eq H (app [T1, x]) (app [T2, x]) (F1 x) (F2 x).
    mk-proof-eq H T1 T2 Codom
      (app [{{@eq_ind_r}}, Ty', T2', (fun _ Ty' (y\ (app [{{ @eq }} , Codom, app [y | L'], T2]))), app [{{@eq_refl}}, Ty, T2], T1', H]) :-
      get-head T1 T1', get-head T2 T2', coq.typecheck T1 Ty ok, coq.typecheck T1' Ty' ok,  names L, std.filter L (x\ occurs x T1) L'.

  % All elpi tactics must use the [solve] predicate. It takes a goal and returns the list of subgoals generated by the tactic.
  % Note that the goal given as input is open, that is, all the variables in the context are considered as eigenvariables.
  % The outputed list of goals contains sealed-goals: that is, functions binding the variables in the context (by an operator called "nabla").
  % When we open new goals by introducing all the eigenvariables that represent the terms in the local context, 
  % the eigenvariables identifiers used in elpi are different that the one used in the previous goals.
  % This poins causes several problem. Indeed, if we work on a context variable [c0] and generate a new goal, 
  % [c0] means nothing for the new goal, as it is not in the program context anymore. An hypothesis with the same Coq identifier
  % and the same type may be in the local context of the new goal, but elpi always chooses a different name. 
  % So maybe it is called [c1] now... Forgetting this is a frequent cause of failure in elpi.
  % This is the reason why we computed the position [N] of our hypothesis [H] in the context: we can retrieve [H] in a new goal 
  % (this will be the [N+1]th hypothesis, as we introduced a new hypothesis at the top of our context). 

  solve ((goal Ctx _ _ _ [trm H]) as Goal) NewGoals :- % I would recommand to look at 
    % https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_tactic.html#defining-tactics to understand the [goal] predicate

    std.do! % [std.do! L] tries to runs everything in [L] and never backtracks
    [coq.typecheck H (app [{{ @eq }}, Ty, T1, T2]) ok, % the given hypothesis should be of type [f = g] 
     mk-proof-eq H T1 T2 Ty R1, % we build the proof term given the initial hypothesis, the functions and their types
     find-pos-in-context Ctx H 0 N, % we find the position of H in the context as we want to clear it in a new goal
     coq.ltac.call "myassert" [trm R1] Goal [NewGoal| _], % we add the proof term in the local context and we get a sealed-goal [NewGoal]
     coq.ltac.open (clear-with-pos (N + 1)) NewGoal NewGoals]. 
    % as the [clear-with-pos] predicate works on open goals, we use the [coq.ltac.open] function to transform NewGoal into its not sealed version
}}.
Elpi Typecheck.


(** elpi introduces new parsing annotations for [Tactic Notation], 
here, we use [ltac_term] but we also have [ltac_term_list] 
if the tactic we defined takes several arguments *)

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