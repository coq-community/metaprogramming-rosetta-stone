open Proofview
open EConstr
open Environ

(* --- Useful higher-order functions --- *)

(* Like List.fold_left, but threading state *)
let fold_left_state f b l sigma =
  List.fold_left (fun (sigma, b) a -> f b a sigma) (sigma, b) l

(* Like fold_left_state, but over arrays *)
let fold_left_state_array f b args =
  fold_left_state f b (Array.to_list args)

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

(* --- Implementation --- *)

(*
 * Inner implementation of autoinduct tactic
 * The current version supports only nested applications, and doesn't support every kind of subterm yet
 *)
let rec do_autoinduct env concl f f_args sigma =
  match kind sigma concl with
  | Constr.App (g, g_args) ->
     if Constr.equal (EConstr.to_constr sigma f) (EConstr.to_constr sigma g) then
       if Array.length f_args = Array.length g_args then
         let _ = lookup_definition env f sigma in
         let _ = Feedback.msg_warning (Pp.str "Found the right term! But autoinduct's app case is not yet fully implemented!") in
         Tacticals.tclIDTAC
       else
         Tacticals.tclIDTAC
     else
       let _, t =
         fold_left_state_array
           (fun _ a sigma ->
             sigma, do_autoinduct env a f f_args sigma)
           Tacticals.tclIDTAC
           g_args
           sigma
       in t
  | _ ->
     Tacticals.tclIDTAC

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

