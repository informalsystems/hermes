------------------------- MODULE counterexample -------------------------

EXTENDS ICS02Tests

(* Initial state *)

State1 ==
TRUE
(* Transition 0 to State2 *)

State2 ==
/\ action = [type |-> "Null"]
/\ actionOutcome = "Null"
/\ clients = 1 :> 0 @@ 2 :> 0 @@ 3 :> 0 @@ 4 :> 0 @@ 5 :> 0
/\ nextClientId = 1

(* Transition 1 to State3 *)

State3 ==
/\ action = [height |-> 1, type |-> "CreateClient"]
/\ actionOutcome = "CreateOK"
/\ clients = 1 :> 1 @@ 2 :> 0 @@ 3 :> 0 @@ 4 :> 0 @@ 5 :> 0
/\ nextClientId = 2

(* Transition 5 to State4 *)

State4 ==
/\ action = [clientId |-> 1, height |-> 1, type |-> "UpdateClient"]
/\ actionOutcome = "UpdateHeightVerificationFailure"
/\ clients = 1 :> 1 @@ 2 :> 0 @@ 3 :> 0 @@ 4 :> 0 @@ 5 :> 0
/\ nextClientId = 2

(* The following formula holds true in the last state and violates the invariant *)

InvariantViolation == actionOutcome = "UpdateHeightVerificationFailure"

================================================================================
\* Created by Apalache on Tue Feb 02 19:12:27 CET 2021
\* https://github.com/informalsystems/apalache
