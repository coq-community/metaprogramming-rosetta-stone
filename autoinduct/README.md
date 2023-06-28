# The `autoinduct` tactic

1. `autoinduct on (f a b).` should run `induction` on the recursive argument of `f`, in this case either `a` or `b`.
   1. `f` unfolds to a `fix`, like `Nat.plus` does
   1. `f` unfolds to `fun ... => fix`, like `List.map does`
   1. `f` reduces (many steps) to the above
1. `autoinduct on f.` as above but the arguments on which `induction` is run are not given. The tactic has to inspect the goal and run `induction` on an actual term.

The tactic should be callable  from the `"Classic"` proof mode, AKA ltac1.

The tactic was originally used in a course by T. Ringer, more information is [here](https://dependenttyp.es/classes/fa2022/artifacts/12-custom.html).

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

## Elpi

The [autoinduct/elpi/](autoinduct/elpi/) directory contains the code of a typical elpi tactic, and the file
[Tactic.v](autoinduct/elpi/theories/Tactic.v) the actual implementation of `autoinduct`.

<details>

<summary>expand</summary>

details specific to the Elpi code

</details>


## LTac2

To compile the Ltac version, you will need [StructTact](https://github.com/uwplse/StructTact).
The code is in [this file](autoinduct/ltac/Ltac2.v)

<details>

<summary>expand</summary>

details specific to the Ltac2 code

</details>
