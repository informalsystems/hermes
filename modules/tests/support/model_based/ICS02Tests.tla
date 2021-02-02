------------------------- MODULE ICS02Tests ---------------------------

EXTENDS ICS02

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