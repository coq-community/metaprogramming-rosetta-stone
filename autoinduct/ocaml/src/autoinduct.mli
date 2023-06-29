(*
 * Interface for implementation of autoinduct tactic, which optionally takes
 * a fixpoint and/or arguments to look for, and performs induction over an
 * argument in the goal corresponding to the recursive argument of that
 * fixpoint (or the first applicable fixpoint it finds, if none is supplied). 
 *)
val autoinduct :
  EConstr.t option -> EConstr.t array option -> unit Proofview.tactic
