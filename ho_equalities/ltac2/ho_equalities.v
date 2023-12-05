From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr.
Import Unsafe.

Ltac2 split_prod (t : constr) :=
  let rec aux t acc :=
    match kind t with
      | Prod bind t' =>
          aux t' ((Binder.name bind, Binder.type bind) :: acc)
      | _ => (acc, t)
    end in aux t [].

Ltac2 fresh_ident_of_option (opt : ident option) :=
  match opt with
    | None => 
        let idH := ident:(H) in
        let frees := Fresh.Free.of_ids [ident:(H)] in
        Fresh.fresh frees idH
    | Some id => id
  end.

Ltac2 rec gen_eq (hyp: ident) (binds :(ident option * constr) list) (b: constr) (f : constr) (g : constr) (l: kind list) () :=
  match binds with
    | [] =>
        let rels := Array.of_list (List.rev (List.map make l)) in
        let f := make (App f rels) in 
        let g := make (App g rels) in
        let arr := Array.of_list [b; f; g] in 
        let trm := make (App constr:(@eq) arr) in 
        let idH := Fresh.in_goal @H in 
        let h := Control.hyp hyp in 
        assert (idH : $trm) by ltac1:(h |- rewrite h ; reflexivity) (Ltac1.of_constr h) ; eapply &idH 
    | (opt, c) :: binds => 
        let id := fresh_ident_of_option opt in 
        let newbinds := List.map (fun (x, y) => (x, substnl [make (Var id)] 0 y)) binds in
        let proof := 
          in_context id c (gen_eq hyp newbinds (substnl [make (Var id)] (List.length binds) b) f g ((Var id) :: l)) in
        let id :=  Fresh.in_goal @H in assert ($id := $proof) ; ltac1:(proof |- try (exact proof)) (Ltac1.of_constr proof)
      end.

Ltac2 eliminate_ho_eq (h : ident) :=
  let t := Control.hyp h in
  match! type t with
    | @eq ?a ?f ?g => 
        let (l, b) := split_prod a in
        gen_eq h (List.rev l) b f g [] () ;
        ltac1:(H |- clear H) (Ltac1.of_constr t)
  end.

Tactic Notation "eliminate_ho_eq" ident(H) := 
  let f := ltac2:(id |- 
  let id2 := Ltac1.to_ident id in 
  let id3 := match id2 with 
      | None => Control.throw (Not_found)
      | Some id3 => id3 
    end in eliminate_ho_eq id3) in f H.

Section tests.

Set Default Proof Mode "Classic".

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