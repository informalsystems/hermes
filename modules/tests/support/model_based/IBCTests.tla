------------------------------ MODULE IBCTests --------------------------------

EXTENDS IBC

\* ICS02CreateClient tests
ICS02CreateOKTest ==
    /\ actionOutcome = "ICS02CreateOK"

\* ICS02UpdateClient tests
ICS02UpdateOKTest ==
    /\ actionOutcome = "ICS02UpdateOK"

ICS02ClientNotFoundTest ==
    /\ actionOutcome = "ICS02ClientNotFound"

ICS02HeaderVerificationFailureTest ==
    /\ actionOutcome = "ICS02HeaderVerificationFailure"

\* ICS03ConnectionOpenInit tests
ICS03ConnectionOpenInitOKTest ==
    /\ actionOutcome = "ICS03ConnectionOpenInitOK"

ICS03MissingClientTest ==
    /\ actionOutcome = "ICS03MissingClient"

\* ICS03ConnectionOpenTry tests
ICS03ConnectionOpenTryOKTest ==
    /\ actionOutcome = "ICS03ConnectionOpenTryOK"

ICS03InvalidConsensusHeightTest ==
    /\ actionOutcome = "ICS03InvalidConsensusHeight"

ICS03ConnectionNotFoundTest ==
    /\ actionOutcome = "ICS03ConnectionNotFound"

ICS03ConnectionMismatchTest ==
    /\ actionOutcome = "ICS03ConnectionMismatch"

ICS03MissingClientConsensusStateTest ==
    /\ actionOutcome = "ICS03MissingClientConsensusState"

\* TODO: the following test should fail but doesn't because proofs are not yet
\*       verified in the implementation
\* ICS03InvalidProofTest ==
\*     /\ actionOutcome = "ICS03InvalidProof"

\* ICS03ConnectionOpenAck tests
ICS03ConnectionOpenAckOKTest ==
    /\ actionOutcome = "ICS03ConnectionOpenAckOK"

ICS03UninitializedConnectionTest ==
    /\ actionOutcome = "ICS03UninitializedConnection"

\* ICS03ConnectionOpenConfirm tests
ICS03ConnectionOpenConfirmOKTest ==
    /\ actionOutcome = "ICS03ConnectionOpenConfirmOK"

===============================================================================
