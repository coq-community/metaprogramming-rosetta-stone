From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr.
Import Unsafe.

(** The main tactic [eliminate_ho_eq] takes a hypothesis which is a 
higher-order equality of the form [f = g]
and generates an proves a new hypothesis [forall x1, ... xn, f x1 ... xn = g x1 ... xn] *)

(** The unsafe module in the Constr file allow us to have access to the 
Coq's kernel terms. In Ltac2, we always need to match on the kind of the constr 
to retrieve its structure. 
To understand how it works, I strongly recommand to look at the source : 
https://github.com/coq/coq/blob/master/user-contrib/Ltac2/Constr.v 

The kernel represents variables either by names ([Var] constructor)
or by their De Brujin index ([Rel] constructor). 
A De Brujin index [n] is an integer which denotes the number 
of binders that are in scope between the variable [Rel n] and 
its corresponding binder.
*)

(** The main function [gen_eq] takes the functions [f] and [g], the type of [f] [tyf],
and a list [l] (the variables [x1 ... xn] which we will 
introduce one by one).

In the base case (we obtained all the arguments for the functions), we build an array containing all 
the arguments [x1 ... xn] and we give it to [f] and [g], getting [f x1 ... xn] and 
[g x1 ... xn].

In the recursive case we create a new variable with De Brujin index 1 (as in the kernel, 
the indexes start by 1), add it to the list of (lifted) variables and recurse under the binder

 *)
Ltac2 rec gen_eq (f: constr) (g : constr) (tyf : constr) (l: int list) :=
  match kind tyf with
    | Prod bind ty => make (Prod bind (gen_eq f g ty (1::List.map (fun x => Int.add x 1) l)))
    | _ => 
        let lrel := List.map (fun x => Rel x) l in
        let lconstr := List.rev (List.map make lrel) in 
        let f_app := make (App f (Array.of_list lconstr)) in
        let g_app := make (App g (Array.of_list lconstr)) in 
        make (App constr:(@eq) (Array.of_list [tyf ; f_app; g_app]))
  end.

(** The main function uses Control.hyp h to retrieve the constr given the 
identifier of the hypothesis [h] and checks that its type is an equality.
It is written [match!] and not [match] because Ltac2 has a low-level match [match]
and a high-level match [match!]. The last one is similar to the one of Ltac1: 
we can directly use the syntax of Coq terms and not the syntax of Ltac2.

Once the function has split the product type (argument [a]), 
a call to the main function is made *)  

Ltac2 eliminate_ho_eq (h : ident) :=
  let t := Control.hyp h in
  match! type t with
    | @eq ?a ?f ?g =>
        let c := gen_eq f g a [] in assert $c 
  end.

(** Tactic Notation is useful to transform Ltac2 functions
into Ltac1 tactics, but we need to use the quotation [ltac2:( arg1 ... arg1 |- ...)] *)

Tactic Notation "eliminate_ho_eq" ident(H) := 
  let f := ltac2:(id |- 
  let id2 := Ltac1.to_ident id in 
  let id3 := match id2 with 
      | None => Control.throw (Not_found)
      | Some id3 => id3 
    end in eliminate_ho_eq id3) in f H.

Section tests.

Set Default Proof Mode "Classic". (* Switchs from Ltac2 to Ltac1 proof mode *)

Goal forall (f g : forall (A B : Type) (a : A) (b : B), A * B) (Heq : f = g), False.
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

End tests.