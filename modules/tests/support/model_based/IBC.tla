--------------------------- MODULE IBC ----------------------------

EXTENDS Integers, FiniteSets, ICS02, ICS03

\* ids of existing chains
CONSTANT ChainIds
\* max number of client to be created per chain
CONSTANT MaxClientsPerChain
ASSUME MaxClientsPerChain > 0
\* max height which clients can reach
CONSTANT MaxClientHeight
ASSUME MaxClientHeight > 0
\* max number of connections to be created per chain
CONSTANT MaxConnectionsPerChain
ASSUME MaxConnectionsPerChain > 0

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
    height |-> Int,
    clientId |-> Int,
    counterpartyClientId |-> Int
]
AsAction(a) == a <: ActionType
(****************** END OF TYPE ANNOTATIONS FOR APALACHE ********************)

\* set of possible client identifiers
ClientIds == 0..(MaxClientsPerChain - 1)
\* set of possible client heights
ClientHeights == 1..MaxClientHeight
\* set of possible connection identifiers
ConnectionIds == 0..(MaxConnectionsPerChain- 1)
\* set of possible connection states
ConnectionStates == {
    "Uninit",
    "Init",
    "TryOpen",
    "Open"
}

\* data kept per cliennt
Client == [
    height: ClientHeights \union {NullHeight}
]
\* mapping from client identifier to its height
Clients == [
    ClientIds -> Client
]
\* data kept per connection
Connection == [
    state: ConnectionStates,
    clientId: ClientIds \union {NullClientId},
    counterpartyClientId: ClientIds \union {NullClientId},
    connectionId: ConnectionIds \union {NullConnectionId},
    counterpartyConnectionId: ConnectionIds \union {NullConnectionId}
]
\* mapping from connection identifier to its data
Connections == [
    ConnectionIds -> Connection
]
\* data kept per chain
Chain == [
    clients: Clients,
    clientIdCounter: 0..MaxClientsPerChain,
    connections: Connections,
    connectionIdCounter: 0..MaxConnectionsPerChain
]
\* mapping from chain identifier to its data
Chains == [
    ChainIds -> Chain
]

\* set of possible actions
NullActions == [
    type: {"Null"}
] <: {ActionType}
CreateClientActions == [
    type: {"ICS02CreateClient"},
    chainId: ChainIds,
    height: ClientHeights
] <: {ActionType}
UpdateClientActions == [
    type: {"ICS02UpdateClient"},
    chainId: ChainIds,
    clientId: ClientIds,
    height: ClientHeights
] <: {ActionType}
ConnectionOpenInitActions == [
    type: {"ICS03ConnectionOpenInit"},
    chainId: ChainIds,
    clientId: ClientIds,
    counterpartyClientId: ClientIds
] <: {ActionType}
Actions ==
    NullActions \union
    CreateClientActions \union
    UpdateClientActions \union
    ConnectionOpenInitActions

\* set of possible action outcomes
ActionOutcomes == {
    "Null",
    "ICS02CreateOK",
    "ICS02UpdateOK",
    "ICS02ClientNotFound",
    "ICS02HeaderVerificationFailure",
    "ICS03ConnectionOpenInitOK",
    "ICS03MissingClient",
    "ModelError"
}

(***************************************************************************
 Specification
 ***************************************************************************)

CreateClient(chainId, clientHeight) ==
    LET chain == chains[chainId] IN
    LET clients == chain.clients IN
    LET clientIdCounter == chain.clientIdCounter IN
    LET result == ICS02_CreateClient(clients, clientIdCounter, clientHeight) IN
    \* update the chain
    LET updatedChain == [chain EXCEPT
        !.clients = result.clients,
        !.clientIdCounter = result.clientIdCounter
    ] IN
    \* update `chains`, set the action and its outcome
    /\ chains' = [chains EXCEPT ![chainId] = updatedChain]
    /\ action' = AsAction([type |-> "ICS02CreateClient",
                           chainId |-> chainId,
                           height |-> clientHeight])
    /\ actionOutcome' = result.outcome

UpdateClient(chainId, clientId, clientHeight) ==
    LET chain == chains[chainId] IN
    LET clients == chain.clients IN
    LET result == ICS02_UpdateClient(clients, clientId, clientHeight) IN
    \* update the chain
    LET updatedChain == [chain EXCEPT
        !.clients = result.clients
    ] IN
    \* update `chains`, set the action and its outcome
    /\ chains' = [chains EXCEPT ![chainId] = updatedChain]
    /\ action' = AsAction([type |-> "ICS02UpdateClient",
                           chainId |-> chainId,
                           clientId |-> clientId,
                           height |-> clientHeight])
    /\ actionOutcome' = result.outcome

ConnectionOpenInit(chainId, clientId, counterpartyClientId) ==
    LET chain == chains[chainId] IN
    LET clients == chain.clients IN
    LET connections == chain.connections IN
    LET connectionIdCounter == chain.connectionIdCounter IN
    LET result == ICS03_ConnectionOpenInit(clients, connections, connectionIdCounter, clientId, counterpartyClientId) IN
    \* update the chain
    LET updatedChain == [chain EXCEPT
        !.connections = result.connections,
        !.connectionIdCounter = result.connectionIdCounter
    ] IN
    /\ chains' = [chains EXCEPT ![chainId] = updatedChain]
    /\ action' = AsAction([type |-> "ICS03ConnectionOpenInit",
                           chainId |-> chainId,
                           clientId |-> clientId,
                           counterpartyClientId |-> counterpartyClientId])
    /\ actionOutcome' = result.outcome

CreateClientAction ==
    \* select a chain id
    \E chainId \in ChainIds:
    \* select a height for the client to be created at
    \E clientHeight \in ClientHeights:
        \* only create client if the model constant `MaxClientsPerChain` allows it
        /\ chains[chainId].clientIdCounter \in ClientIds
        /\ CreateClient(chainId, clientHeight)

UpdateClientAction ==
    \* select a chain id
    \E chainId \in ChainIds:
    \* select a client to be updated (which may not exist)
    \E clientId \in ClientIds:
    \* select a height for the client to be updated
    \E clientHeight \in ClientHeights:
        UpdateClient(chainId, clientId, clientHeight)

ConnectionOpenInitAction ==
    \* select a chain id
    \E chainId \in ChainIds:
    \* select a client id
    \E clientId \in ClientIds:
    \* select a couterparty client id
    \E counterpartyClientId \in ClientIds:
        \* only create connection if the model constant `MaxConnectionsPerChain` allows it
        /\ chains[chainId].connectionIdCounter \in ConnectionIds
        /\ ConnectionOpenInit(chainId, clientId, counterpartyClientId)

Init ==
    \* create an null client and a null connection
    LET nullClient == [
        height |-> NullHeight
    ] IN
    LET nullConnection == [
        state |-> "Uninit",
        clientId |-> NullClientId,
        counterpartyClientId |-> NullClientId,
        connectionId |-> NullConnectionId,
        counterpartyConnectionId |-> NullConnectionId
    ] IN
    \* create an empty chain
    LET emptyChain == [
        clients |-> [clientId \in ClientIds |-> nullClient],
        clientIdCounter |-> 0,
        connections |-> [connectionId \in ConnectionIds |-> nullConnection],
        connectionIdCounter |-> 0
    ] IN
    /\ chains = [chainId \in ChainIds |-> emptyChain]
    /\ action = AsAction([type |-> "Null"])
    /\ actionOutcome = "Null"

Next ==
    \/ CreateClientAction
    \/ UpdateClientAction
    \/ ConnectionOpenInitAction
    \/ UNCHANGED <<chains, action, actionOutcome>>

(***************************************************************************
 Invariants
 ***************************************************************************)

TypeOK ==
    /\ chains \in Chains
    /\ action \in Actions
    /\ actionOutcome \in ActionOutcomes

\* the model never erros
ModelNeverErrors ==
    actionOutcome /= "ModelError"

=============================================================================
