open Proofview
open EConstr

(*
 * Inner implementation of autoinduct tactic
 *)
let do_autoinduct env concl i sigma =
  match kind sigma concl with
  | Constr.App (f, args) ->
     let _ = Feedback.msg_warning (Pp.str "Autoinduct's app case is not yet implemented!") in
     Tacticals.tclIDTAC
  | _ ->
     CErrors.user_err (Pp.str "Only immediate applications in autoinduct are currently supported")

(*
 * Implementation of autoinduct tactic, top level
 *)
let autoinduct i =
  Goal.enter begin fun gl ->
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    let concl = Goal.concl gl in
    do_autoinduct env concl i sigma
  end

