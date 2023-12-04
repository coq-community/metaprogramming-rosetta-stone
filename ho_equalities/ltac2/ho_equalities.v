From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr.
Import Unsafe.
Set Default Proof Mode "Classic".
Set Printing Existential Instances.
Set Printing Goal Names.

Goal True.
let H := fresh in epose (H := ?[x] : ?[Goal]).
refine (_ _).  Focus 2.
instantiate (Goal2 := nat).




 assert H. unfold H.
instantiate (x := (forall (A : Type), A)). intros A.
refine ( _ _). Focus 2. exact H. *) 
(* 
Ltac2 rec make_binder_list (l : (ident option * constr) list) :=
  match l with
    | [] => []
    | (id, a) :: l => Binder.unsafe_make id Binder.Relevant a :: make_binder_list l
  end. *)


Ltac2 split_prod (t : constr) :=
  let rec aux t acc :=
    match kind t with
      | Prod bind t' =>
          aux t' ((Binder.name bind, Binder.type bind) :: acc)
      | _ => (acc, t)
    end in aux t [].

Ltac2 rec gen_eq (hyp: constr) (binds :(ident option * constr) list) (b: constr) (f : constr) (g : constr) (l: kind list) () :=
Message.print (Message.of_string "test") ;
  match binds with
    | [] =>
        let idH := ident:(H) in 
        let frees := Fresh.Free.of_ids [ident:(H)] in 
        let rels := Array.of_list (List.rev (List.map make l)) in
        let f := make (App f rels) in Message.print (Message.of_constr f) ;
        let g := make (App g rels) in
        let arr := Array.of_list [b; f; g] in 
        let trm := make (App constr:(@eq) arr) in 
          ltac1:(term |- instantiate (Goal0 := term)) (Ltac1.of_constr trm)
        (* assert (id : $trm) *) (* by (rewrite $hyp; reflexivity) ; Std.revert [idH] *)
    | (opt, c) :: binds => 
        let id :=
          match opt with
            | None => 
                let idH := ident:(H) in
                let frees := Fresh.Free.of_ids [ident:(H)] in
                Fresh.fresh frees idH
            | Some id => id
          end in  Message.print (Message.of_constr c) ;
        let newbinds := List.map (fun (x, y) => (x, substnl [make (Var id)] 0 y)) binds in
        let proof := 
          in_context id c (gen_eq hyp newbinds b f g ((Var id) :: l)) in
        let frees := Fresh.Free.of_ids [@proof] in
        let id := Fresh.fresh frees @proof in assert (id := $proof)
      end.


Ltac2 eliminate_ho_eq (t : constr) :=
  match! type t with
    | @eq ?a ?f ?g => 
        let (l, b) := split_prod a in
        gen_eq t (List.rev l) b f g [] ()
  end.
        
  
        
        (* 
        let new_eq := make (Prod bind 
        




        let f' := (liftn 1 0 f) in
        let g' := (liftn 1 0 g) in
        (Prod bind (make (gen_eq l b f' g' (0 :: (List.map (fun x => Int.add x 1) rels))))) 
  end.
 
Ltac2 rec gen_eq (l : binder list) (b: constr) (f: constr) (g: constr) (rels: int list) :=
  match l with
    | [] => 
        let vars := Array.map (fun x => make (Rel x)) (Array.of_list rels) in
        let arr := Array.of_list [b; make (App f vars); make (App g vars)] in
        (App constr:(@eq) arr)
    | bind :: l =>
        let f' := (liftn 1 0 f) in
        let g' := (liftn 1 0 g) in
        (Prod bind (make (gen_eq l b f' g' (0 :: (List.map (fun x => Int.add x 1) rels))))) 
  end.
     *)
(* constr list -> int -> constr -> constr *)

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
  end) by reflexivity.  eliminate_ho_eq 'H. intro. intro. reflexivity.
assert (H1 : Nat.add =
fix add (n m : nat) {struct n} : nat :=
  match n with
  | 0 => m
  | S p => S (add p m)
  end) by reflexivity. eliminate_ho_eq H1.
eliminate_ho_eq Heq.
Abort.

End tests.