(** The main tactic [eliminate_ho_eq] takes a hypothesis which is a 
higher-order equality of the form [f = g]
and generates an proves a new hypothesis [forall x1, ... xn, f x1 ... xn = g x1 ... xn] *)

(** One of the main difficulty of Ltac is that we can't work easily 
under binders.Try to write a Ltac function which counts the number of (prenex) quantifiers
in a term to convince yourself !

In order to implement our tactic, we have to cross an arbitrary number of binders, 
because the functions we consider have an unknown number [n] of arguments.
But Ltac syntax is high-level, we can't access to the internal representation 
of a Coq term.
We can write easily a non-generic tactic which works for functions with 1, 2, 3 ... arguments.
However, there is a trick to always work on function with one argument, and to 
avoid the problem: uncurrying ! 
Thus, the tactic recurses on a function which takes a dependent pair (of the form [{ x : A & P x}])
In the end, the first projection of the pair should contain all the arguments of the function except the last one.
The last argument is then contained in the second projection.

In addition, the syntax [@?f x] allows us to use patterns which mentions 
variables. Here, [f] is indeed a metavariable (i.e.: a variable which has to be unified 
with a concrete Coq term) which can see [x]. *)


Inductive default :=.

Ltac get_uncurry_eq A := 
  let rec tac_rec A := (* A is a function taking a dependent pair and returning the equality between f and g *)
  lazymatch constr:(A) with
    | fun p => @eq (forall (x : @?B p), @?body p x) (@?f p) (@?g p) => 
        tac_rec ltac:(eval cbv beta in (* we need to reduce the term because the pattern matching of Ltac is purely
  syntactic, so not up to reduction *)
        (fun (p : {x & B x})  => @eq (body (projT1 p) (projT2 p)) (f (projT1 p) (projT2 p)) (g (projT1 p) (projT2 p))))
    | ?C =>  C
  end in tac_rec (fun _: default => A).
(* the function we start with takes a dumb default value because 
we always need two types to build dependent pairs *)

(** After calling get_uncurry_eq on a higher-order equality f = g, 
we get a term of the form
[(fun p : {x1 : {x2 : { ... { xn : default & Pn } ...} } } =>
 f (projT2 (projT1 (projT1 ... (projT1 p)... ))) ... (projT2 (projT1 p)) ... (projT2 p) =
 g (projT2 (projT1 (projT1 ... (projT1 p)... ))) ... (projT2 (projT1 p)) ... (projT2 p)]

The next step is to curry it, and to remove the useless argument of type [default].

The next function [dependent_curry_eq] does precise reductions, because 
we need to reduce the term in order to use the syntactical match of Ltac, 
but not too much, because we may unfold a constant we do not want to 
For instance, if we work on an equality between a constant and its body; we 
do not want to unfold the constant, otherwise the two members of the equality will 
become syntactically equal. *)


Ltac dependent_curry_eq t :=
  lazymatch t with
    | forall (_ : default), ?h => constr:(h) (* removing the default argument *)
    | fun (y: { x : _ & @?P x}) => @?body y =>
        dependent_curry_eq 
        ltac:(let t := eval cbv beta in (forall a b, body (existT _ a b)) in
        let t' := eval unfold projT1 in t in eval unfold projT2 in t') (* we should match this branch in the first call 
of the function, as it binds only one argument *)
   | forall (y: { x : _ & @?P x}) (z : @?Q y), @?body y z  =>
        dependent_curry_eq 
        ltac:(let t := eval cbv beta in (forall a b (c : Q (existT _ a b)), body (existT _ a b) c) in 
              let t' := eval unfold projT1 in t in eval unfold projT2 in t') (* we should match this branch in the
following calls. Note that it is crucial to mention the variable z of type Q y, as it depends on the previous binder 
(a dependent pair) *)
    | _ => ltac:(let t' := eval unfold projT1 in t 
                 in eval unfold projT2 in t')
  end.


(** The last tactic [eliminate_ho_eq] is trivial, it combines the previous steps 
and proves the statement with a really small proof script *) 

Ltac eliminate_ho_eq H :=
  let T := type of H in 
  let T' := get_uncurry_eq T in
  let T'' := dependent_curry_eq T' in 
  let H0 := fresh H in 
  assert (H0 : T'') by (intros ; rewrite H ; reflexivity); clear H.
 
Section tests.

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
eliminate_ho_eq Heq.
Abort.

End tests.
