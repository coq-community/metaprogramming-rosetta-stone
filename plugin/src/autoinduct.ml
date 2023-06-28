open Proofview
open EConstr
open Environ

(* --- Useful higher-order functions --- *)

let bind f1 f2 = (fun sigma -> let sigma, a = f1 sigma in f2 a sigma) 
let ret a = fun sigma -> sigma, a

(* Stateful if/else *)
let branch_state p f g a =
  bind
    (fun sigma_f ->
      bind
        (p a)
        (fun b sigma_t -> ret b (if b then sigma_t else sigma_f))
        sigma_f)
    (fun b -> if b then f a else g a)

(* Like List.fold_left, but threading state *)
let fold_left_state f b l sigma =
  List.fold_left (fun (sigma, b) a -> f b a sigma) (sigma, b) l

(* fold_left2 with state *)
let fold_left2_state f c l1 l2 sigma =
  List.fold_left2 (fun (sigma, c) a b -> f c a b sigma) (ret c sigma) l1 l2

(* Like fold_left_state, but over arrays *)
let fold_left_state_array f b args =
  fold_left_state f b (Array.to_list args)

(* Like fold_left2_state, but over arrays *)
let fold_left2_state_array f c args1 args2 sigma =
  fold_left2_state f c (Array.to_list args1) (Array.to_list args2) sigma

(* Stateful forall2 *)
let forall2_state_array p args1 args2 =
  fold_left2_state_array
    (fun b a1 a2 -> branch_state (p a1) (fun _ -> ret b) (fun _ -> ret false) a2)
    true
    args1
    args2

(* --- Useful Coq utilities --- *)

(*
 * Look up a definition from an environment
 *)
let lookup_definition env def sigma =
  match kind sigma def with
  | Constr.Const (c, u) ->
     let cb = lookup_constant c env in
     (match Global.body_of_constant_body Library.indirect_accessor cb with
      | Some(e, _, _) -> EConstr.of_constr e
      | None -> CErrors.user_err (Pp.str "The supplied term is not a function"))
  | _ -> CErrors.user_err (Pp.str "The supplied term is not a function")

(* Equal but convert to constr (maybe this exists already in the Coq API *)
let eequal trm1 trm2 sigma =
  sigma, Constr.equal (EConstr.to_constr sigma trm1) (EConstr.to_constr sigma trm2)

(* Push a local binding to an environment *)
let push_local (n, t) env =
  EConstr.push_rel Context.Rel.Declaration.(LocalAssum (n, t)) env

(* --- Implementation --- *)

(*
 * Get the recursive argument index
 *)
let rec recursive_argument env f_body sigma =
  match kind sigma f_body with
  | Constr.Fix ((rec_indexes, i), _) -> Array.get rec_indexes i
  | Constr.Lambda (n, t, b) ->
     let env_b = push_local (n, t) env in
     1 + (recursive_argument env_b b sigma)
  | Constr.Const (c, u) ->
     recursive_argument env (lookup_definition env f_body sigma) sigma
  | _ ->
     CErrors.user_err (Pp.str "The supplied function is not a ")

(*
 * Inner implementation of autoinduct tactic
 * The current version supports only nested applications, and doesn't support every kind of subterm yet
 * It also does not have any useful error message when it doesn't find the function; it just does idtac
 * It also requires exact equality (rather than convertibility) for the function and all of its arguments
 * It also doesn't stop itself if the chosen argument is a constant, and doesn't backtrack
 *)
let rec do_autoinduct env concl f f_args sigma =
  match kind sigma concl with
  | Constr.App (g, g_args) ->
     let sigma, f_eq = eequal f g sigma in
     if f_eq then
       if Array.length f_args = Array.length g_args then
         let sigma, args_eq = forall2_state_array eequal f_args g_args sigma in
         if args_eq then 
           let f_body = lookup_definition env f sigma in
           let arg_no = recursive_argument env f_body sigma in
           let arg = Array.get g_args arg_no in
           let dest_arg = (Some true), Tactics.ElimOnConstr (fun env sigma -> sigma, (arg, Tactypes.NoBindings)) in
           Tactics.induction_destruct true false ([(dest_arg, (None, None), None)], None)
         else
           Tacticals.tclFAIL (Pp.str "Wrong number of arguments")
       else
         Tacticals.tclFAIL (Pp.str "Could not find an occurrence of the supplied function")
     else
       let _, t =
         fold_left_state_array
           (fun t a sigma ->
             sigma, Tacticals.tclOR t (do_autoinduct env a f f_args sigma))
           (Tacticals.tclFAIL (Pp.str "No arguments were supplied"))
           g_args
           sigma
       in t
  | _ ->
     Tacticals.tclFAIL (Pp.str "Could not find anything to induct over")

(*
 * Implementation of autoinduct tactic, top level
 *)
let autoinduct f f_args =
  Goal.enter begin fun gl ->
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    let concl = Goal.concl gl in
    do_autoinduct env concl f f_args sigma 
  end

