# The `autoinduct` tactic

This exercise amounts to implementing a tactic which performs induction on the right argument of a recursive function.
The tactic was originally used in a course by T. Ringer, more information is [here](https://dependenttyp.es/classes/fa2022/artifacts/12-custom.html).

## Steps
1. `autoinduct on (f a b).` should run `induction` on the recursive argument of `f`, in this case either `a` or `b`.
   1. `f` unfolds to a `fix`, like `Nat.plus` does
   1. `f` unfolds to `fun ... => fix`, like `List.map does`
   1. `f` reduces (many steps) to the above
   2. `f` takes any number of arguments, not just two
1. `autoinduct on f.` as above but the arguments on which `induction` is run are not given. The tactic has to inspect the goal and run `induction` on an actual term.
2. `autoinduct` as above but finds the first `f` in the goal for which we can run an induction

The tactic should be callable  from the `"Classic"` proof mode, AKA ltac1.

# Example

```coq
Fixpoint add_left (n m : nat) : nat :=
  match n with
  | O => m
  | S p => S (add_left p m)
  end.

Lemma add_left_O : forall (n : nat), add_left n O = n.
Proof.
  intros.
  autoinduct on (add_left n O).
  all: (simpl; congruence).
Qed.
```

# Solutions

## OCaml

The code is in [this file](ocaml/src/autoinduct.ml)

<details>

<summary>expand</summary>

details specific to the OCaml code

</details>

## LTac1

To compile the Ltac version, you will need [StructTact](https://github.com/uwplse/StructTact).
The code is in [this file](ltac/Ltac1.v)

<details>

<summary>expand</summary>

Setails specific to the Ltac1 code.

About extracting the recursive argument:
- the match construct lets one access the recursive argument `n` of a fix
  as in `fix f _ _ {struct n} := _ end`, but does not support multiple arities.
  Hence one needs to provide multiple patterns, eg `fix f _ _ _ {struct n} := _ end`
  for ternary functions, and so on.

</details>

## LTac2

The code is in [this file](ltac/Ltac2.v)

<details>

<summary>expand</summary>

Some details specific to the Ltac2 code.

About extracting the recursive argument:
- the code uses APIs in the `Unsafe` namespace to access the raw
  syntax of terms. This makes the code work for any arity.



</details>


## Elpi

The [autoinduct/elpi/](elpi/) directory contains the code of a typical elpi tactic and the file
[Tactic.v](elpi/theories/Tactic.v) the actual implementation of `autoinduct`.

<details>

<summary>expand</summary>

Some details specific to the Elpi code.

About extracting the recursive argument:
- whilst elpi supports Coq syntax within quotations,
  `{{ fix f _ _ {struct N} := _ end }}` does not let one bind `N`, so the code
  uses the raw term ast `fix _ _ N _` to extract the index of the recursive
  argument
- since we look at the term ast, the code works for any arity of `f`

</details>

## MetaCoq

The [code](metacoq/theories/Autoinduct.v)

<details>

<summary>expand</summary>

Some details specific to the MetaCoq code.

</details>
