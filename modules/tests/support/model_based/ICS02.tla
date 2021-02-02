--------------------------- MODULE ICS02 ----------------------------

EXTENDS Integers, FiniteSets

\* max number of client to be created
CONSTANT MaxClients
ASSUME MaxClients > 0
\* max height which clients can reach
CONSTANT MaxHeight
ASSUME MaxHeight > 0

\* set of client data
VARIABLE clients
\* counter used to generate client identifiers
VARIABLE clientIdCounter
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
ClientIds == 0..(MaxClients - 1)
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
    IF ClientExists(clientIdCounter) THEN
        \* if the client to be created already exists,
        \* then there's an error in the model
        /\ actionOutcome' = "ModelError"
        /\ UNCHANGED <<clients, clientIdCounter>>
    ELSE
        \* set the new client's height to `clientHeight`
        /\ clients' = SetClientHeight(clientIdCounter, clientHeight)
        \* update `clientIdCounter`
        /\ clientIdCounter' = clientIdCounter + 1
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
            /\ UNCHANGED <<clientIdCounter>>
        ELSE
            /\ actionOutcome' = "UpdateHeightVerificationFailure"
            /\ UNCHANGED <<clients, clientIdCounter>>
    ELSE
        \* if the client does not exist, then return an error
        /\ actionOutcome' = "UpdateClientNotFound"
        /\ UNCHANGED <<clients, clientIdCounter>>

CreateClientAction ==
    \* only create client if the model constant `MaxClients` allows it
    /\ clientIdCounter \in ClientIds
    \* select a height for the client to be created at
    /\ \E clientHeight \in Heights:
        /\ CreateClient(clientHeight)
        /\ action' = AsAction([type |-> "CreateClient",
                               height |-> clientHeight])

UpdateClientAction ==
    \* select a client to be updated (which may not exist)
    \E clientId \in ClientIds:
        \* select a height for the client to be updated
        \E clientHeight \in Heights:
            /\ UpdateClient(clientId, clientHeight)
            /\ action' = AsAction([type |-> "UpdateClient",
                                   clientId |-> clientId,
                                   height |-> clientHeight])

 Init ==
    /\ clients = [clientId \in ClientIds |-> NullHeight]
    /\ clientIdCounter = 0
    /\ action = AsAction([type |-> "Null"])
    /\ actionOutcome = "Null"

Next ==
    \/ CreateClientAction
    \/ UpdateClientAction
    \/ UNCHANGED <<clients, clientIdCounter, action, actionOutcome>>

(***************************************************************************
 Invariants
 ***************************************************************************)

TypeOK ==
    /\ clientIdCounter \in 0..MaxClients
    /\ clients \in [ClientIds -> Heights \union {NullHeight}]
    /\ action \in Actions
    /\ actionOutcome \in ActionOutcomes

\* the model never erros
ModelNeverErrors ==
    actionOutcome /= "ModelError"

=============================================================================
