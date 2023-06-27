(*
 * Interface for implementation of autoinduct tactic
 *)
val autoinduct : EConstr.t -> EConstr.t array -> unit Proofview.tactic
