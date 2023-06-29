From Coq Require Import ZArith.
From elpi Require Import elpi.
From AC Require Import AC.

(******************************************************************************)
(* The Z_zmodule tactic                                                       *)
(******************************************************************************)

Ltac Z_zmodule_reflection VM ZE1 ZE2 :=
  apply (@ZM_correct_Z VM ZE1 ZE2); [vm_compute; reflexivity].

Elpi Tactic Z_zmodule.
Elpi Accumulate lp:{{

pred mem o:list term, o:term, o:term.
mem [X|_] X {{ O }} :- !.
mem [_|XS] X {{ S lp:N }} :- !, mem XS X N.

pred quote i:term, o:term, o:list term.
quote {{ Z0 }} {{ AGO }} _ :- !.
quote {{ Z.opp lp:In1 }} {{ AGOpp lp:Out1 }} VM :- !, quote In1 Out1 VM.
quote {{ Z.add lp:In1 lp:In2 }} {{ AGAdd lp:Out1 lp:Out2 }} VM :- !,
  quote In1 Out1 VM, quote In2 Out2 VM.
quote In {{ AGX lp:N }} VM :- !, mem VM In N.

pred list-constant o:term, o:list term, o:term.
list-constant T [] {{ @nil lp:T }} :- !.
list-constant T [X|XS] {{ @cons lp:T lp:X lp:XS' }} :- list-constant T XS XS'.

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
