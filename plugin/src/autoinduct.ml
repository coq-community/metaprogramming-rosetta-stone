(*
 * Implementation of autoinduct tactic
 *)
let autoinduct i =
  Proofview.Goal.enter begin fun gl ->
    let _ = Feedback.msg_warning (Pp.str "Autoinduct is not yet implemented!") in
    Tacticals.tclIDTAC
  end
