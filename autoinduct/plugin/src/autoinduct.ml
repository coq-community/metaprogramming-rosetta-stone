open Proofview
open EConstr
open Environ

(* --- Useful higher-order functions, mostly from https://github.com/uwplse/coq-plugin-lib --- *)

(* Like List.fold_left, but threading state *)
let fold_left_state f b l sigma =
  List.fold_left (fun (sigma, b) a -> f b a sigma) (sigma, b) l

(* Like fold_left_state, but over arrays *)
let fold_left_state_array f b args =
  fold_left_state f b (Array.to_list args)

(* --- Useful Coq utilities, adapted from coq-plugin-lib with help from Gaetan --- *)

(*
 * Look up a definition from an environment
 *)
let lookup_definition env def sigma =
  match kind sigma def with
  | Constr.Const (c, u) ->
     begin match constant_value_in env (c, EConstr.Unsafe.to_instance u) with
     | v -> EConstr.of_constr v
     | exception NotEvaluableConst _ ->
         CErrors.user_err (Pp.str "The supplied term is not a transparent constant.")
     end
  | _ -> CErrors.user_err (Pp.str "The supplied term is not a constant.")

(* Equal but convert to constr (maybe this exists already in the Coq API) *)
let eequal trm1 trm2 sigma =
  sigma, EConstr.eq_constr sigma trm1 trm2

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
     CErrors.user_err (Pp.str "The supplied function is not a fixpoint")

(*
 * Inner implementation of autoinduct tactic
 * The current version supports just nested applications for now
 * It's Part 2 out of 3, so requires explicit arguments
 * It also does not have the most useful error messages
 * It also requires exact equality (rather than convertibility) for the function and all of its arguments
 * It also may not stop itself if the chosen argument is not inductive (have not tested yet; it may, actually)
 *)
let rec do_autoinduct env concl f sigma =
  match kind sigma concl with
  | Constr.App (g, g_args) ->
     let sigma, f_eq = eequal f g sigma in
     if f_eq then
       let f_body = lookup_definition env f sigma in
       let arg_no = recursive_argument env f_body sigma in
       if arg_no < Array.length g_args then
         let arg = Array.get g_args arg_no in
         let dest_arg = (Some true), Tactics.ElimOnConstr (fun env sigma -> sigma, (arg, Tactypes.NoBindings)) in
         Tactics.induction_destruct true false ([(dest_arg, (None, None), None)], None)
       else
         Tacticals.tclFAIL (Pp.str "Wrong number of arguments")
     else
       let _, t =
         fold_left_state_array
           (fun t a sigma ->
             sigma, Tacticals.tclOR t (do_autoinduct env a f sigma))
           (Tacticals.tclFAIL (Pp.str "Function is not applied to any arguments"))
           g_args
           sigma
       in t
  | _ ->
     Tacticals.tclFAIL (Pp.str "Could not find anything to induct over")

(*
 * Implementation of autoinduct tactic, top level
 *)
let autoinduct f =
  Goal.enter begin fun gl ->
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    let concl = Goal.concl gl in
    do_autoinduct env concl f sigma 
  end

