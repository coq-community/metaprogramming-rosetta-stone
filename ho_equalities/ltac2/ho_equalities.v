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

(** This auxilary function will help us to retrieve the type of the two equal functions.
We split the product between each argument domain and the codomain. 
The [Prod] constructor takes a binder (namely a name, a type and a relevance) 
and a constr to make a new constr. The relevance is only useful when you work in SProp, 
otherwise you will do fine by using the relevance Binder.Relevant *)

Ltac2 split_prod (t : constr) :=
  let rec aux t acc :=
    match kind t with
      | Prod bind t' =>
          aux t' ((Binder.name bind, Binder.type bind) :: acc)
      | _ => (acc, t)
    end in aux t [].

(** This function helps us to get a fresh ident starting from
an ident option. Note that the annotation [@H] 
(or [ident:(H)] as a shorthand) allows to quote [H] as an ident in Ltac2.
Fresh.free_of_ids generates the list of the free variables in an ident, 
and Fresh.fresh generates an ident starting to a given one ([@H])
which does not belong to a set of free variables (here, [frees]). *)
 

Ltac2 fresh_ident_of_option (opt : ident option) :=
  match opt with
    | None =>
        let frees := Fresh.Free.of_ids [@H] in
        Fresh.fresh frees @H
    | Some id => id
  end.

(** The main function [gen_eq] takes an ident [hyp] which is the one of the premise [f = g], 
a list of binders (the name and the type of the arguments of the functions), the codomain [b],
[f] and [g] our functions, and a list of kind [l] (the variables [x1 ... xn] which we will 
introduce one by one). It also expects a term of type unit because this function is in fact a thunk, 
evaluated only for its side effects on the proof state. 

In the base case (we obtained all the arguments for the functions), we build an array containing all 
the arguments [x1 ... xn] and we give it to [f] and [g], getting [f x1 ... xn] and 
[g x1 ... xn].
We build the desired equality [equ] and we assert it. 
We designate this hypothesis of type [equ] by a new ident [idH].
The proof of [equ] is made by a small Ltac2 script: [rewrite $h; reflexivity].
Here, we use [$h] because [rewrite] takes a Coq term. Thus, [$] performs 
an antiquotation from the constr of Ltac2 to the underlying Coq term.

The last tactic of the base case, [eapply &idH], will become clearer once we looked at the recursive
case. It is here because when we reach the base case, we are not in the main goal. The goal here is 
just a metavariable of any type. So we should then precise our goal, and thus we say that it is [&idH],
the Coq term designated by the ident [idH], which is of type [trm].

In the recursive case, we introduce a new constr which is a named variable: [make (Var id)], of type [a].
Consequently, we should substitute the De Brujin index 0 contained in [f], in [g], in [b] and in the 
type of the other binders by [make (Var id)]. 
We cannot work directly on De Brujin indexes because each time we call the function [make]
to build a constr from a kind, [make] will perform a type-checking. So if a term contains free variables, 
the type-checking will fail, producing a fatal error. 
In my opinion, this leads to a lot of difficulties, making Ltac2 a language 
that I do NOT recommend to use for working with De Brujin indexes. But still, we will 
find a solution in this tutorial.

The trick is to use [in_context id c tac], which runs a tactic [tac] on a new goal (a metavariable of any type),
keeping the same hypotheses as the previous goal, but with a new hypothesis id : c, and returns the term
[fun (id : c) => t], where [t] is a proof of the new arbitrary goal.
This explains the line [let proof := in_context ... ]. We can retrieve the proof [t] of [f x1 ... xn = g xn ... xn], 
created in a context in which [x1 ... xn] are bound, and abstrating it to [fun x1 ... xn => t]. 
In order to keep this proof in each recursive call (where the goal is also a metavariable [?Goal]), we
prove [?Goal] by [exact proof]. Here, we used Ltac1 inside ltac2, to show the syntax to call Ltac1 tactics.
We write [ltac1:(tac)] for tactics taking no arguments, and [ltac1:(arg1 ... argn |- tac)]
otherwise. In the second case, the arguments should be of type Ltac1.t, so we perform some casts.
Indeed, our function uses [Ltac1.of_constr].

 *)

Ltac2 rec gen_eq (hyp: ident) (binds :(ident option * constr) list) (b: constr) (f : constr) (g : constr) (l: kind list) () :=
  match binds with
    | [] =>
        let rels := Array.of_list (List.rev (List.map make l)) in
        let f := make (App f rels) in 
        let g := make (App g rels) in
        let arr := Array.of_list [b; f; g] in 
        let equ := make (App constr:(@eq) arr) in 
        let idH := Fresh.in_goal @H in 
        let h := Control.hyp hyp in 
        assert (idH : $equ) by (rewrite $h; reflexivity) ; eapply &idH 
    | (opt, a) :: binds => 
        let id := fresh_ident_of_option opt in 
        let newbinds := List.map (fun (x, y) => (x, substnl [make (Var id)] 0 y)) binds in
        let proof := 
          in_context id a (gen_eq hyp newbinds (substnl [make (Var id)] (List.length binds) b) f g ((Var id) :: l)) in
        let id :=  Fresh.in_goal @H in assert ($id := $proof) ; ltac1:(proof |- try (exact proof)) (Ltac1.of_constr proof)
      end.

(** The main function uses Control.hyp h to retrieve the constr given the 
identifier of the hypothesis [h] and checks that its type is an equality.
It is written [match!] and not [match] because Ltac2 has a low-level match [match]
and a high-level match [match!]. The last one is similar to the one of Ltac1: 
we can directly use the syntax of Coq terms and not the syntax of Ltac2.

Once the function has split the product type (argument [a]), 
a call to the main function is made, and the last thing to do is to clear the previous
hypothesis which is presumed to be not useful anymore *)  

Ltac2 eliminate_ho_eq (h : ident) :=
  let t := Control.hyp h in
  match! type t with
    | @eq ?a ?f ?g => 
        let (l, b) := split_prod a in
        gen_eq h (List.rev l) b f g [] () ;
        ltac1:(H |- clear H) (Ltac1.of_constr t)
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