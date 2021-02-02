--------------------------- MODULE ICS02 ----------------------------

EXTENDS Integers, FiniteSets

\* max client identifier
CONSTANT MaxClientId
ASSUME MaxClientId > 0
\* max height which clients can reach
CONSTANT MaxHeight
ASSUME MaxHeight > 0

\* set of client data
VARIABLE clients
\* counter used to generate client identifiers
VARIABLE nextClientId
\* last action performed
VARIABLE action
\* string with the outcome of the last operation
VARIABLE actionOutcome

(********************* TYPE ANNOTATIONS FOR APALACHE ***********************)
\* operator for type annotations
a <: b == a

ActionType == [
    type |-> STRING,
    clientId |-> Int,
    height |-> Int
]
AsAction(a) == a <: ActionType
(****************** END OF TYPE ANNOTATIONS FOR APALACHE ********************)

\* set of possible client identifiers
ClientIds == 1..MaxClientId
\* set of possible heights
Heights == 1..MaxHeight
\* if a client has a null height then the client does not exist
NullHeight == 0
\* set of possible actions
NullActions == [
    type: {"Null"}
] <: {ActionType}
CreateClientActions == [
    type: {"CreateClient"},
    height: Heights
] <: {ActionType}
UpdateClientActions == [
    type: {"UpdateClient"},
    clientId: ClientIds,
    height: Heights
] <: {ActionType}
Actions == NullActions \union CreateClientActions \union UpdateClientActions
\* set of possible outcomes
ActionOutcomes == {"Null", "CreateOK", "UpdateOK", "UpdateClientNotFound", "UpdateHeightVerificationFailure", "ModelError"}


(***************************************************************************
 Specification
 ***************************************************************************)

\* check if a client exists
ClientExists(clientId) ==
    clients[clientId] /= NullHeight

SetClientHeight(clientId, clientHeight) ==
    [clients EXCEPT ![clientId] = clientHeight]

CreateClient(clientHeight) ==
    \* check if the client exists (it shouldn't)
    IF ClientExists(nextClientId) THEN
        \* if the client to be created already exists,
        \* then there's an error in the model
        /\ actionOutcome' = "ModelError"
        /\ UNCHANGED <<clients, nextClientId>>
    ELSE
        \* set the new client's height to `clientHeight`
        /\ clients' = SetClientHeight(nextClientId, clientHeight)
        \* update `nextClientId`
        /\ nextClientId' = nextClientId + 1
        \* set `outcome`
        /\ actionOutcome' = "CreateOK"

UpdateClient(clientId, clientHeight) ==
    \* check if the client exists
    IF ClientExists(clientId) THEN
        \* if the client exists, check its height
        IF clients[clientId] < clientHeight THEN
            \* if its height is lower than the one being updated to
            \* then, update the client
            /\ clients' = SetClientHeight(clientId, clientHeight)
            \* set outcome
            /\ actionOutcome' = "UpdateOK"
            /\ UNCHANGED <<nextClientId>>
        ELSE
            /\ actionOutcome' = "UpdateHeightVerificationFailure"
            /\ UNCHANGED <<clients, nextClientId>>
    ELSE
        \* if the client does not exist, then return an error
        /\ actionOutcome' = "UpdateClientNotFound"
        /\ UNCHANGED <<clients, nextClientId>>

CreateClientAction ==
    \* only create client if the model constant `MaxClientId` allows it
    /\ nextClientId < MaxClientId
    \* select a height for the client to be created at
    /\ \E clientHeight \in Heights:
        /\ action' = AsAction([type |-> "CreateClient",
                               height |-> clientHeight])
        /\ CreateClient(clientHeight)

UpdateClientAction ==
    \* select a client to be updated (which may not exist)
    \E clientId \in ClientIds:
        \* select a height for the client to be updated
        \E clientHeight \in Heights:
            /\ action' = AsAction([type |-> "UpdateClient",
                                   clientId |-> clientId,
                                   height |-> clientHeight])
            /\ UpdateClient(clientId, clientHeight)

 Init ==
    /\ clients = [clientId \in ClientIds |-> NullHeight]
    /\ nextClientId = 1
    /\ action = AsAction([type |-> "Null"])
    /\ actionOutcome = "Null"

Next ==
    \/ CreateClientAction
    \/ UpdateClientAction
    \/ UNCHANGED <<clients, nextClientId, action, actionOutcome>>

(***************************************************************************
 Invariants
 ***************************************************************************)

TypeOK ==
    /\ nextClientId \in ClientIds \union {MaxClientId + 1}
    /\ clients \in [ClientIds -> Heights \union {NullHeight}]
    /\ action \in Actions
    /\ actionOutcome \in ActionOutcomes

\* the model never erros
ModelNeverErrors ==
    actionOutcome /= "ModelError"

=============================================================================
