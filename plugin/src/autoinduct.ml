open Proofview

(*
 * Implementation of autoinduct tactic
 *)
let do_autoinduct env i sigma =
  let _ = Feedback.msg_warning (Pp.str "Autoinduct is not yet implemented!") in
  Tacticals.tclIDTAC

(*
 * Implementation of autoinduct tactic, top level
 *)
let autoinduct i =
  Goal.enter begin fun gl ->
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    do_autoinduct env i sigma
  end
