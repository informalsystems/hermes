------------------------------ MODULE IBCTests --------------------------------

EXTENDS IBC

ICS02CreateOKTest ==
    /\ actionOutcome = "ICS02CreateOK"

ICS02UpdateOKTest ==
    /\ actionOutcome = "ICS02UpdateOK"

ICS02ClientNotFoundTest ==
    /\ actionOutcome = "ICS02ClientNotFound"

ICS02HeaderVerificationFailureTest ==
    /\ actionOutcome = "ICS02HeaderVerificationFailure"

ICS02CreateOKTestNeg == ~ICS02CreateOKTest
ICS02UpdateOKTestNeg == ~ICS02UpdateOKTest
ICS02ClientNotFoundTestNeg == ~ICS02ClientNotFoundTest
ICS02HeaderVerificationFailureTestNeg == ~ICS02HeaderVerificationFailureTest

===============================================================================
