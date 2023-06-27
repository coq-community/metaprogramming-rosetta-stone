(*
 * Implementation of autoinduct tactic
 *)
let autoinduct i =
  let _ = Feedback.msg_warning (Pp.str "Autoinduct is not yet implemented!") in
  Tacticals.tclIDTAC
