--------------------------------- MODULE IBC ----------------------------------

EXTENDS Integers, FiniteSets, ICS02, ICS03

\* ids of existing chains
CONSTANT ChainIds
\* max number of client to be created per chain
CONSTANT MaxClientsPerChain
ASSUME MaxClientsPerChain >= 0
\* max height which clients can reach
CONSTANT MaxClientHeight
ASSUME MaxClientHeight >= 0
\* max number of connections to be created per chain
CONSTANT MaxConnectionsPerChain
ASSUME MaxConnectionsPerChain >= 0

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
    height |-> Int,
    clientId |-> Int,
    counterpartyClientId |-> Int
]
AsAction(a) == a <: ActionType
(******************* END OF TYPE ANNOTATIONS FOR APALACHE ********************)

\* set of possible chain heights
ChainHeights == Int
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
    height: ClientHeights \union {HeightNone}
]
\* mapping from client identifier to its height
Clients == [
    ClientIds -> Client
]
\* data kept per connection
Connection == [
    state: ConnectionStates,
    clientId: ClientIds \union {ClientIdNone},
    counterpartyClientId: ClientIds \union {ClientIdNone},
    connectionId: ConnectionIds \union {ConnectionIdNone},
    counterpartyConnectionId: ConnectionIds \union {ConnectionIdNone}
]
\* mapping from connection identifier to its data
Connections == [
    ConnectionIds -> Connection
]
\* data kept per chain
Chain == [
    \* height: ChainHeights,
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
NoneActions == [
    type: {"None"}
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
    NoneActions \union
    CreateClientActions \union
    UpdateClientActions \union
    ConnectionOpenInitActions

\* set of possible action outcomes
ActionOutcomes == {
    "None",
    "ICS02CreateOK",
    "ICS02UpdateOK",
    "ICS02ClientNotFound",
    "ICS02HeaderVerificationFailure",
    "ICS03ConnectionOpenInitOK",
    "ICS03MissingClient",
    "ModelError"
}

(***************************** Specification *********************************)

CreateClient(chainId, clientHeight) ==
    LET chain == chains[chainId] IN
    LET clients == chain.clients IN
    LET clientIdCounter == chain.clientIdCounter IN
    LET result == ICS02_CreateClient(clients, clientIdCounter, clientHeight) IN
    \* update the chain
    LET updatedChain == [chain EXCEPT
        \* !.height = @ + 1,
        !.clients = result.clients,
        !.clientIdCounter = result.clientIdCounter
    ] IN
    \* update `chains`, set the `action` and its `actionOutcome`
    /\ chains' = [chains EXCEPT ![chainId] = updatedChain]
    /\ action' = AsAction([
        type |-> "ICS02CreateClient",
        chainId |-> chainId,
        height |-> clientHeight])
    /\ actionOutcome' = result.outcome

UpdateClient(chainId, clientId, clientHeight) ==
    LET chain == chains[chainId] IN
    LET clients == chain.clients IN
    LET result == ICS02_UpdateClient(clients, clientId, clientHeight) IN
    \* update the chain
    LET updatedChain == [chain EXCEPT
        \* !.height = @ + 1,
        !.clients = result.clients
    ] IN
    \* update `chains`, set the `action` and its `actionOutcome`
    /\ chains' = [chains EXCEPT ![chainId] = updatedChain]
    /\ action' = AsAction([
        type |-> "ICS02UpdateClient",
        chainId |-> chainId,
        clientId |-> clientId,
        height |-> clientHeight])
    /\ actionOutcome' = result.outcome

ConnectionOpenInit(chainId, clientId, counterpartyClientId) ==
    LET chain == chains[chainId] IN
    LET clients == chain.clients IN
    LET connections == chain.connections IN
    LET connectionIdCounter == chain.connectionIdCounter IN
    LET result == ICS03_ConnectionOpenInit(
        clients,
        connections,
        connectionIdCounter,
        clientId,
        counterpartyClientId
    ) IN
    \* update the chain
    LET updatedChain == [chain EXCEPT
        \* !.height = @ + 1,
        !.connections = result.connections,
        !.connectionIdCounter = result.connectionIdCounter
    ] IN
    \* update `chains`, set the `action` and its `actionOutcome`
    /\ chains' = [chains EXCEPT ![chainId] = updatedChain]
    /\ action' = AsAction([
        type |-> "ICS03ConnectionOpenInit",
        chainId |-> chainId,
        clientId |-> clientId,
        counterpartyClientId |-> counterpartyClientId])
    /\ actionOutcome' = result.outcome

ConnectionOpenTry(chainId, clientId, counterpartyClientId, connectionId) ==
    LET chain == chains[chainId] IN
    LET clients == chain.clients IN
    LET connections == chain.connections IN
    LET connectionIdCounter == chain.connectionIdCounter IN
    LET result == ICS03_ConnectionOpenTry(
        clients,
        connections,
        connectionIdCounter,
        clientId,
        counterpartyClientId,
        connectionId
    ) IN
    UNCHANGED vars

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

ConnectionOpenInitAction ==
    \* select a chain id
    \E chainId \in ChainIds:
    \* select a client id
    \E clientId \in ClientIds:
    \* select a counterparty client id
    \E counterpartyClientId \in ClientIds:
        \* only create connection if the model constant `MaxConnectionsPerChain`
        \* allows it
        IF chains[chainId].connectionIdCounter \in ConnectionIds THEN
            ConnectionOpenInit(chainId, clientId, counterpartyClientId)
        ELSE
            UNCHANGED vars

ConnectionOpenTryAction ==
    \* select a chain id
    \E chainId \in ChainIds:
    \* select a client id
    \E clientId \in ClientIds:
    \* select a counterparty client id
    \E counterpartyClientId \in ClientIds:
    \* select a connection id (which can be none)
    \E connectionId \in ConnectionIds \union {ConnectionIdNone}:
        IF connectionId = ConnectionIdNone THEN
            \* in this case we're trying to create a new connection; only create
            \* connection if the model constant `MaxConnectionsPerChain` allows
            \* it
            IF chains[chainId].connectionIdCounter \in ConnectionIds THEN
                ConnectionOpenTry(
                    chainId,
                    clientId,
                    counterpartyClientId,
                    connectionId
                )
            ELSE
                UNCHANGED vars
        ELSE
            ConnectionOpenTry(
                chainId,
                clientId,
                counterpartyClientId,
                connectionId
            )

Init ==
    \* create a client and a connection with none values
    LET clientNone == [
        height |-> HeightNone
    ] IN
    LET connectionNone == [
        state |-> "Uninit",
        clientId |-> ClientIdNone,
        counterpartyClientId |-> ClientIdNone,
        connectionId |-> ConnectionIdNone,
        counterpartyConnectionId |-> ConnectionIdNone
    ] IN
    \* create an empty chain
    LET emptyChain == [
        \* height |-> 0,
        clients |-> [clientId \in ClientIds |-> clientNone],
        clientIdCounter |-> 0,
        connections |-> [connectionId \in ConnectionIds |-> connectionNone],
        connectionIdCounter |-> 0
    ] IN
    /\ chains = [chainId \in ChainIds |-> emptyChain]
    /\ action = AsAction([type |-> "None"])
    /\ actionOutcome = "None"

Next ==
    \/ CreateClientAction
    \/ UpdateClientAction
    \/ ConnectionOpenInitAction
    \/ ConnectionOpenTryAction
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
