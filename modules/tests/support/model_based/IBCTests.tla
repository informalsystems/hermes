------------------------- MODULE IBCTests ---------------------------

EXTENDS IBC

CreateOK ==
    /\ actionOutcome = "CreateOK"

UpdateOK ==
    /\ actionOutcome = "UpdateOK"

UpdateClientNotFound ==
    /\ actionOutcome = "UpdateClientNotFound"

UpdateHeightVerificationFailure ==
    /\ actionOutcome = "UpdateHeightVerificationFailure"

CreateOKTest == ~CreateOK
UpdateOKTest == ~UpdateOK
UpdateClientNotFoundTest == ~UpdateClientNotFound
UpdateHeightVerificationFailureTest == ~UpdateHeightVerificationFailure

=============================================================================