open Proofview
open EConstr
open Environ

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
         CErrors.user_err (Pp.str "The supplied term is not a transparent constant")
     end
  | _ -> CErrors.user_err (Pp.str "The supplied term is not a constant")

(* Equal but convert to constr (maybe this exists already in the Coq API) *)
let eequal trm1 trm2 sigma =
  sigma, EConstr.eq_constr sigma trm1 trm2

(* Push a local binding to an environment *)
let push_local (n, t) env =
  EConstr.push_rel Context.Rel.Declaration.(LocalAssum (n, t)) env

(* --- Implementation --- *)

(*
 * Get the recursive argument index of the fixpoint defined by f
 * Return None if f is not a fixpoint
 *)
let rec recursive_index env f sigma =
  match kind sigma f with
  | Constr.Fix ((rec_indexes, i), _) ->
     Some (Array.get rec_indexes i)
  | Constr.Lambda (n, t, b) ->
     let env_b = push_local (n, t) env in
     Option.map (fun n -> 1 + n) (recursive_index env_b b sigma)
  | Constr.Const (c, u) ->
     recursive_index env (lookup_definition env f sigma) sigma
  | _ ->
     None

(*
 * Get the function to unfold and check if it is a fixpoint
 * (This could be an Option.fold, but that would add OCaml version dependencies)
 *)
let function_to_unfold f_opt g =
  match f_opt with
  | Some f -> f
  | None -> g

(*
 * Get the recursive argument to supply to autoinduct
 * Return None if not found
 *)
let recursive_argument env concl f_opt sigma =
  match kind sigma concl with
  | Constr.App (g, g_args) ->
     let f = function_to_unfold f_opt g in
     let sigma, f_eq = eequal f g sigma in
     if f_eq then
       let arg_opt =
         Option.bind
           (recursive_index env f sigma)
           (fun arg_no ->
             if arg_no < Array.length g_args then
               Some (Array.get g_args arg_no)
             else
               None)
       in sigma, arg_opt
     else
       sigma, None
  | _ ->
     sigma, None
  
(*
 * Inner implementation of autoinduct tactic
 * The current version:
 * 1. does not go under binders,
 * 2. supports both part 2 and part 3,
 * 3. checks exact equality (rather than convertibility) for part 2,
 * 4. does not have the best error handling yet.
 *)
let find_autoinduct env concl f_opt sigma : Evd.evar_map * (EConstr.t list) =
  let rec aux under_binders (sigma, found) concl =
    if under_binders then
      sigma, found
    else
      let sigma, arg_opt = recursive_argument env concl f_opt sigma in
      let found =
        match arg_opt with
        | Some arg ->
           arg :: found
        | None ->
           found
      in EConstr.fold_with_binders sigma (fun _ -> true) aux under_binders (sigma, found) concl
  in aux false (sigma, []) concl

(*
 * Given the argument to induct over, invoke the induction tactic
 *)
let induct_on arg =
  let dest_arg = Some true, Tactics.ElimOnConstr (fun _ sigma -> sigma, (arg, Tactypes.NoBindings)) in
  Tactics.induction_destruct true false ([dest_arg, (None, None), None], None)

(*
 * Find possible arguments to suggest inducting over
 * Try just the first one (which is last in the list of arguments)
 *)
let do_autoinduct env concl f_opt sigma =
  let sigma, induct_args = find_autoinduct env concl f_opt sigma in
  if CList.is_empty induct_args then
    Tacticals.tclFAIL (Pp.str "Could not find anything to induct over")
  else
    tclBIND
      (Proofview.Unsafe.tclEVARS sigma)
      (fun () -> Tacticals.tclFIRST (List.map induct_on (List.rev induct_args)))

(*
 * Implementation of autoinduct tactic, top level
 *)
let autoinduct f_opt =
  Goal.enter begin fun gl ->
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    let concl = Goal.concl gl in
    do_autoinduct env concl f_opt sigma
  end

