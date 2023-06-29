open Proofview
open EConstr
open Environ

(* --- Useful utilities, adapted from coq-plugin-lib --- *)

(*
 * Return a1 if a1_opt is Some a1; otherwise return a2.
 * This could be an Option.fold, but that would add OCaml version dependencies.
 *)
let get_with_default a1_opt a2 =
  match a1_opt with
  | Some a1 -> a1
  | None -> a2

(* Look up a definition from an environment *)
let lookup_definition env def sigma =
  match kind sigma def with
  | Constr.Const (c, u) ->
     begin match constant_value_in env (c, EConstr.Unsafe.to_instance u) with
     | v -> EConstr.of_constr v
     | exception NotEvaluableConst _ ->
         CErrors.user_err (Pp.str "The supplied term is not a transparent constant")
     end
  | _ -> CErrors.user_err (Pp.str "The supplied term is not a constant")

(* Equal, but with evar_map tracking for defense against later changes *)
let eequal trm1 trm2 sigma : Evd.evar_map * bool =
  sigma, EConstr.eq_constr sigma trm1 trm2

(* Equality between all elements of two lists *)
let all_eequal trms1 trms2 sigma : Evd.evar_map * bool =
  if Array.length trms1 = Array.length trms2 then
    List.fold_left2
      (fun (sigma, b) trm1 trm2 ->
        let sigma, trms_eq = eequal trm1 trm2 sigma in
        sigma, b && trms_eq)
      (sigma, true)
      (Array.to_list trms1)
      (Array.to_list trms2)
  else
    sigma, false

(* Push a local binding to an environment *)
let push_local (n, t) env =
  EConstr.push_rel Context.Rel.Declaration.(LocalAssum (n, t)) env

(* --- Implementation --- *)

(*
 * Get the recursive argument index of the fixpoint defined by f.
 * Return None if f is not a fixpoint.
 *)
let rec recursive_index env f sigma =
  match kind sigma f with
  | Constr.Fix ((rec_indexes, i), _) ->
     (* get the recursive argument *)
     Some (Array.get rec_indexes i)
  | Constr.Lambda (n, t, b) ->
     (* add parameters to the environment and recurse on the body *)
     let env_b = push_local (n, t) env in
     Option.map (fun n -> 1 + n) (recursive_index env_b b sigma)
  | Constr.Const (c, u) ->
     (* look up the constant's body and recurse *)
     recursive_index env (lookup_definition env f sigma) sigma
  | _ ->
     (* give up *)
     None

(*
 * Get a recursive argument to the appropriate fixpoint to supply to autoinduct.
 * Return None if not found.
 *)
let recursive_argument env concl f_opt args_opt sigma =
  match kind sigma concl with
  | Constr.App (g, g_args) ->
     let f = get_with_default f_opt g in
     let args = get_with_default args_opt g_args in
     let sigma, f_eq = eequal f g sigma in
     let sigma, args_eq = all_eequal args g_args sigma in
     if f_eq && args_eq then
       (* the function is the correct applied fixpoint; find the argument *)
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
       (* the function is not the correct applied fixpoint; return None *)
       sigma, None
  | _ ->
     (* the goal term does not apply a function at all *)
     sigma, None
  
(*
 * Inner implementation of autoinduct tactic.
 *
 * The current version:
 * 1. does not go under binders,
 * 2. supports all parts at once,
 * 3. checks exact equality (rather than convertibility) for earlier parts, and
 * 4. does not have the best error handling yet.
 *
 * The options here deal with the flexibility in input format, since we
 * handle all three parts at once.
 *
 * The call to fold_with_binders is found in EConstr in the Coq OCaml API.
 * This is a fold over subterms so that we don't need to manually define
 * the trivial behavior of other kinds of subterms. The current implementation
 * just stops immmediately if under binders (inside a Lambda or Prod) because
 * this is easier to start with. If we want to support fancier goals
 * with applications under product types, we can change our call to
 * fold_with_binders, but notably we will need to shift the found arguments
 * since everything here is de Bruijn indexed.
 *)
let find_autoinduct env concl f_opt args_opt sigma =
  let rec aux bound (sigma, found) concl =
    if bound then
      (* do not handle binders yet *)
      sigma, found
    else
      (* find any applicable arguments to induct over *)
      let sigma, arg_opt = recursive_argument env concl f_opt args_opt sigma in
      let found =
        match arg_opt with
        | Some arg ->
           arg :: found
        | None ->
           found
      in fold_with_binders sigma (fun _ -> true) aux bound (sigma, found) concl
  in aux false (sigma, []) concl

(*
 * Given the argument to induct over, invoke the induction tactic.
 *)
let induct_on arg =
  let dest_arg = Some true, Tactics.ElimOnConstr (fun _ sigma -> sigma, (arg, Tactypes.NoBindings)) in
  Tactics.induction_destruct true false ([dest_arg, (None, None), None], None)

(*
 * Find possible arguments to suggest inducting over.
 * Try just the first suggested one (which is last in the list of arguments).
 * If there are not any good candidates, fail with an error message.
 *)
let do_autoinduct env concl f_opt args_opt sigma =
  let sigma, induct_args = find_autoinduct env concl f_opt args_opt sigma in
  if CList.is_empty induct_args then
    Tacticals.tclFAIL (Pp.str "Could not find anything to induct over")
  else
    tclBIND
      (Proofview.Unsafe.tclEVARS sigma)
      (fun () -> Tacticals.tclFIRST (List.map induct_on (List.rev induct_args)))

(*
 * Implementation of autoinduct tactic, top level.
 * This enters the tactic monad, gets the environment and state, and calls
 * the core autoinduct logic, which returns the appropriate tactic.
 *)
let autoinduct f_opt args_opt =
  Goal.enter begin fun gl ->
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    let concl = Goal.concl gl in
    do_autoinduct env concl f_opt args_opt sigma
  end

