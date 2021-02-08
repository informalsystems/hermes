--------------------------------- MODULE IBC ----------------------------------

EXTENDS Integers, FiniteSets, ICS02

\* ids of existing chains
CONSTANT ChainIds
\* max number of client to be created per chain
CONSTANT MaxClientsPerChain
ASSUME MaxClientsPerChain >= 0
\* max height which clients can reach
CONSTANT MaxClientHeight
ASSUME MaxClientHeight >= 0

\* mapping from chain id to its data
VARIABLE chains
\* last action performed
VARIABLE action
\* string with the outcome of the last operation
VARIABLE actionOutcome
vars == <<chains, action, actionOutcome>>

(********************** TYPE ANNOTATIONS FOR APALACHE ************************)
\* operator for type annotations
a <: b == a

ActionType == [
    type |-> STRING,
    chainId |-> STRING,
    clientHeight |-> Int,
    clientId |-> Int
]
AsAction(a) == a <: ActionType
(******************* END OF TYPE ANNOTATIONS FOR APALACHE ********************)

\* set of possible chain heights
ChainHeights == Int
\* set of possible client identifiers
ClientIds == 0..(MaxClientsPerChain - 1)
\* set of possible client heights
ClientHeights == 1..MaxClientHeight

\* data kept per cliennt
Client == [
    height: ClientHeights \union {HeightNone}
]
\* mapping from client identifier to its height
Clients == [
    ClientIds -> Client
]
\* data kept per chain
Chain == [
    height: ChainHeights,
    clients: Clients,
    clientIdCounter: 0..MaxClientsPerChain
]
\* mapping from chain identifier to its data
Chains == [
    ChainIds -> Chain
]

\* set of possible actions
NoneActions == [
    type: {"None"}
] <: {ActionType}
CreateClientActions == [
    type: {"ICS02CreateClient"},
    chainId: ChainIds,
    clientHeight: ClientHeights
] <: {ActionType}
UpdateClientActions == [
    type: {"ICS02UpdateClient"},
    chainId: ChainIds,
    clientHeight: ClientHeights,
    clientId: ClientIds
] <: {ActionType}
Actions ==
    NoneActions \union
    CreateClientActions \union
    UpdateClientActions

\* set of possible action outcomes
ActionOutcomes == {
    "None",
    "ModelError",
    \* ICS02_CreateClient outcomes:
    "ICS02CreateOK",
    \* ICS02_UpdateClient outcomes:
    "ICS02UpdateOK",
    "ICS02ClientNotFound",
    "ICS02HeaderVerificationFailure"
}

(***************************** Specification *********************************)

\* update chain height if outcome was ok
UpdateChainHeight(height, outcome, okOutcome) ==
    IF outcome = okOutcome THEN height + 1 ELSE height

CreateClient(chainId, clientHeight) ==
    LET chain == chains[chainId] IN
    LET clients == chain.clients IN
    LET clientIdCounter == chain.clientIdCounter IN
    LET result == ICS02_CreateClient(clients, clientIdCounter, clientHeight) IN
    \* update the chain
    LET updatedChain == [chain EXCEPT
        !.height = UpdateChainHeight(@, result.outcome, "ICS02CreateOK"),
        !.clients = result.clients,
        !.clientIdCounter = result.clientIdCounter
    ] IN
    \* update `chains`, set the `action` and its `actionOutcome`
    /\ chains' = [chains EXCEPT ![chainId] = updatedChain]
    /\ action' = AsAction([
        type |-> "ICS02CreateClient",
        chainId |-> chainId,
        clientHeight |-> clientHeight])
    /\ actionOutcome' = result.outcome

UpdateClient(chainId, clientId, clientHeight) ==
    LET chain == chains[chainId] IN
    LET clients == chain.clients IN
    LET result == ICS02_UpdateClient(clients, clientId, clientHeight) IN
    \* update the chain
    LET updatedChain == [chain EXCEPT
        !.height = UpdateChainHeight(@, result.outcome, "ICS03CreateOK"),
        !.clients = result.clients
    ] IN
    \* update `chains`, set the `action` and its `actionOutcome`
    /\ chains' = [chains EXCEPT ![chainId] = updatedChain]
    /\ action' = AsAction([
        type |-> "ICS02UpdateClient",
        chainId |-> chainId,
        clientId |-> clientId,
        clientHeight |-> clientHeight])
    /\ actionOutcome' = result.outcome

CreateClientAction ==
    \* select a chain id
    \E chainId \in ChainIds:
    \* select a height for the client to be created at
    \E clientHeight \in ClientHeights:
        \* only create client if the model constant `MaxClientsPerChain` allows
        \* it
        IF chains[chainId].clientIdCounter \in ClientIds THEN
            CreateClient(chainId, clientHeight)
        ELSE
            UNCHANGED vars

UpdateClientAction ==
    \* select a chain id
    \E chainId \in ChainIds:
    \* select a client to be updated (which may not exist)
    \E clientId \in ClientIds:
    \* select a height for the client to be updated
    \E clientHeight \in ClientHeights:
        UpdateClient(chainId, clientId, clientHeight)

Init ==
    \* create a client with none values
    LET clientNone == [
        height |-> HeightNone
    ] IN
    \* create an empty chain
    LET emptyChain == [
        height |-> 0,
        clients |-> [clientId \in ClientIds |-> clientNone],
        clientIdCounter |-> 0
    ] IN
    /\ chains = [chainId \in ChainIds |-> emptyChain]
    /\ action = AsAction([type |-> "None"])
    /\ actionOutcome = "None"

Next ==
    \/ CreateClientAction
    \/ UpdateClientAction
    \/ UNCHANGED vars

(******************************** Invariants *********************************)

TypeOK ==
    /\ chains \in Chains
    /\ action \in Actions
    /\ actionOutcome \in ActionOutcomes

\* the model never erros
ModelNeverErrors ==
    actionOutcome /= "ModelError"

===============================================================================
