From Coq Require Import ZArith.
From elpi Require Import elpi.
From AC Require Import AC.

(******************************************************************************)
(* Tactics specific to Z                                                      *)
(******************************************************************************)

Elpi Db Z_reify lp:{{

pred quote i:term, o:term, o:list term.
quote {{ Z0 }} {{ AGO }} _ :- !.
quote {{ Z.opp lp:In1 }} {{ AGOpp lp:Out1 }} VM :- !, quote In1 Out1 VM.
quote {{ Z.add lp:In1 lp:In2 }} {{ AGAdd lp:Out1 lp:Out2 }} VM :- !,
  quote In1 Out1 VM, quote In2 Out2 VM.
quote In {{ AGX lp:N }} VM :- !, mem VM In N.

pred mem o:list term, o:term, o:term.
mem [X|_] X {{ O }} :- !.
mem [_|XS] X {{ S lp:N }} :- !, mem XS X N.

pred list-constant o:term, o:list term, o:term.
list-constant T [] {{ @nil lp:T }} :- !.
list-constant T [X|XS] {{ @cons lp:T lp:X lp:XS' }} :- list-constant T XS XS'.

}}.

(* The Z_zmodule tactic *)

Ltac Z_zmodule_reflection VM ZE1 ZE2 :=
  apply (@ZM_correct_Z VM ZE1 ZE2); [vm_compute; reflexivity].

Elpi Tactic Z_zmodule.
Elpi Accumulate Db Z_reify.
Elpi Accumulate lp:{{

pred solve i:goal, o:list sealed-goal.
solve (goal _ _ {{ @eq Z lp:T1 lp:T2 }} _ _ as Goal) GS :- !,
  quote T1 ZE1 VM, !,
  quote T2 ZE2 VM, !,
  list-constant {{ Z }} VM VM', !,
  zmod-reflection VM' ZE1 ZE2 Goal GS.
solve _ _ :- coq.ltac.fail 0 "The goal is not an equation".

pred zmod-reflection i:term, i:term, i:term, i:goal, o:list sealed-goal.
zmod-reflection VM ZE1 ZE2 G GS :-
  coq.ltac.call "Z_zmodule_reflection" [trm VM, trm ZE1, trm ZE2] G GS.
zmod-reflection _ _ _ _ _ :-
  coq.ltac.fail 0 "Not a valid Z-module equation".

}}.
Elpi Typecheck.

Tactic Notation "Z_zmodule" := (elpi Z_zmodule).

(* The Z_zmodule_simplify tactic *)

Ltac Z_zmodule_simplify_reflection VM ZE1 ZE2 :=
  let zero := fresh "zero" in
  let add := fresh "add" in
  let vm := fresh "vm" in
  let zeroE := fresh "zeroE" in
  let addE := fresh "addE" in
  let vmE := fresh "vmE" in
  let norm := fresh "norm" in
  apply (@ZMsimpl_correct_Z VM ZE1 ZE2);
  intros zero add vm zeroE addE vmE norm;
  vm_compute in norm; compute;
  rewrite zeroE, addE, vmE; clear zero add vm zeroE addE vmE norm.

Elpi Tactic Z_zmodule_simplify.
Elpi Accumulate Db Z_reify.
Elpi Accumulate lp:{{

pred solve i:goal, o:list sealed-goal.
solve (goal _ _ {{ @eq Z lp:T1 lp:T2 }} _ _ as Goal) GS :- !,
  quote T1 ZE1 VM, !,
  quote T2 ZE2 VM, !,
  list-constant {{ Z }} VM VM', !,
  zmod-simpl-reflection VM' ZE1 ZE2 Goal GS.
solve _ _ :- coq.ltac.fail 0 "The goal is not an equation".

pred zmod-simpl-reflection i:term, i:term, i:term, i:goal, o:list sealed-goal.
zmod-simpl-reflection VM ZE1 ZE2 G GS :-
  coq.ltac.call "Z_zmodule_simplify_reflection" [trm VM, trm ZE1, trm ZE2] G GS.
zmod-simpl-reflection _ _ _ _ _ :-
  coq.ltac.fail 0 "Reflection failed".

}}.
Elpi Typecheck.

Tactic Notation "Z_zmodule_simplify" := (elpi Z_zmodule_simplify).

Goal forall x y y' z, y = y' -> (x + y + - z + y = x + - z + y + y')%Z.
Proof.
intros x y y' z Hy.
Z_zmodule_simplify.
exact Hy.
Qed.
