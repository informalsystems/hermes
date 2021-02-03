--------------------------- MODULE IBC ----------------------------

EXTENDS Integers, FiniteSets

\* ids of existing chains
CONSTANT ChainIds
\* max number of client to be created
CONSTANT MaxClientsPerChain
ASSUME MaxClientsPerChain > 0
\* max height which clients can reach
CONSTANT MaxClientHeight
ASSUME MaxClientHeight > 0

\* mapping from chain id to its data
VARIABLE chains
\* last action performed
VARIABLE action
\* string with the outcome of the last operation
VARIABLE actionOutcome

(********************* TYPE ANNOTATIONS FOR APALACHE ***********************)
\* operator for type annotations
a <: b == a

ActionType == [
    type |-> STRING,
    chainId |-> STRING,
    clientId |-> Int,
    height |-> Int
]
AsAction(a) == a <: ActionType
(****************** END OF TYPE ANNOTATIONS FOR APALACHE ********************)

\* set of possible client identifiers
ClientIds == 0..(MaxClientsPerChain - 1)
\* set of possible client heights
ClientHeights == 1..MaxClientHeight
\* if a client has a null height then the client does not exist
NullHeight == 0

Clients == [
    ClientIds -> ClientHeights \union {NullHeight}
]
Chain == [
    clientIdCounter: 0..MaxClientsPerChain,
    clients: Clients
]

\* set of possible actions
NullActions == [
    type: {"Null"}
] <: {ActionType}
CreateClientActions == [
    type: {"CreateClient"},
    chainId: ChainIds,
    height: ClientHeights
] <: {ActionType}
UpdateClientActions == [
    type: {"UpdateClient"},
    chainId: ChainIds,
    clientId: ClientIds,
    height: ClientHeights
] <: {ActionType}
Actions ==
    NullActions \union
    CreateClientActions \union
    UpdateClientActions

\* set of possible action outcomes
ActionOutcomes == {
    "Null",
    "CreateOK",
    "UpdateOK",
    "UpdateClientNotFound",
    "UpdateHeightVerificationFailure",
    "ModelError"
}

(***************************************************************************
 Specification
 ***************************************************************************)

\* retrieves `clientId`'s height
GetClientHeight(clients, clientId) ==
    clients[clientId]

\* check if a `clientId` exists
ClientExists(clients, clientId) ==
    GetClientHeight(clients, clientId) /= NullHeight

\* update the heigth of `clientId` to `clientHeight`
SetClientHeight(clients, clientId, clientHeight) ==
    [clients EXCEPT ![clientId] = clientHeight]

CreateClient(chainId, clientHeight) ==
    LET clients == chains[chainId].clients
        clientIdCounter == chains[chainId].clientIdCounter IN
    \* check if the client exists (it shouldn't)
    IF ClientExists(clients, clientIdCounter) THEN
        \* if the client to be created already exists,
        \* then there's an error in the model
        /\ actionOutcome' = "ModelError"
        /\ UNCHANGED <<chains>>
    ELSE
        LET chain == [
            \* set the new client's height to `clientHeight`
            clients |-> SetClientHeight(clients, clientIdCounter, clientHeight),
            \* update `clientIdCounter`
            clientIdCounter |-> clientIdCounter + 1
        ] IN
        \* update `chains`
        /\ chains' = [chains EXCEPT ![chainId] = chain]
        \* set `outcome`
        /\ actionOutcome' = "CreateOK"

UpdateClient(chainId, clientId, clientHeight) ==
    LET clients == chains[chainId].clients
        clientIdCounter == chains[chainId].clientIdCounter IN
    \* check if the client exists
    IF ClientExists(clients, clientId) THEN
        \* if the client exists, check its height
        IF GetClientHeight(clients, clientId) < clientHeight THEN
            \* if its height is lower than the one being updated to
            \* then, update the client
            LET chain == [
                \* set the client's height to `clientHeight`
                clients |-> SetClientHeight(clients, clientId, clientHeight),
                \* keep `clientIdCounter`
                clientIdCounter |-> clientIdCounter
            ] IN
            \* update `chains`
            /\ chains' = [chains EXCEPT ![chainId] = chain]
            \* set outcome
            /\ actionOutcome' = "UpdateOK"
        ELSE
            /\ actionOutcome' = "UpdateHeightVerificationFailure"
            /\ UNCHANGED <<chains>>
    ELSE
        \* if the client does not exist, then return an error
        /\ actionOutcome' = "UpdateClientNotFound"
        /\ UNCHANGED <<chains>>

CreateClientAction ==
    \* select a chain
    \E chainId \in ChainIds:
        \* only create client if the model constant `MaxClientsPerChain` allows it
        /\ chains[chainId].clientIdCounter \in ClientIds
        \* select a height for the client to be created at
        /\ \E clientHeight \in ClientHeights:
            /\ CreateClient(chainId, clientHeight)
            /\ action' = AsAction([type |-> "CreateClient",
                                   chainId |-> chainId,
                                   height |-> clientHeight])

UpdateClientAction ==
    \* select a chain
    \E chainId \in ChainIds:
        \* select a client to be updated (which may not exist)
        \E clientId \in ClientIds:
            \* select a height for the client to be updated
            \E clientHeight \in ClientHeights:
                /\ UpdateClient(chainId, clientId, clientHeight)
                /\ action' = AsAction([type |-> "UpdateClient",
                                       chainId |-> chainId,
                                       clientId |-> clientId,
                                       height |-> clientHeight])

Init ==
    \* create an empty chain
    LET emptyChain == [
        clients |-> [clientId \in ClientIds |-> NullHeight],
        clientIdCounter |-> 0
    ] IN
    /\ chains = [chainId \in ChainIds |-> emptyChain]
    /\ action = AsAction([type |-> "Null"])
    /\ actionOutcome = "Null"

Next ==
    \/ CreateClientAction
    \/ UpdateClientAction
    \/ UNCHANGED <<chains, action, actionOutcome>>

(***************************************************************************
 Invariants
 ***************************************************************************)

TypeOK ==
    /\ chains \in [ChainIds -> Chain]
    /\ action \in Actions
    /\ actionOutcome \in ActionOutcomes

\* the model never erros
ModelNeverErrors ==
    actionOutcome /= "ModelError"

=============================================================================
