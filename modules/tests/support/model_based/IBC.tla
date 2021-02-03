--------------------------- MODULE IBC ----------------------------

EXTENDS Integers, FiniteSets

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
\* if a client identifier is undefined then it is -1
NullClientId == -1
\* set of possible client heights
ClientHeights == 1..MaxClientHeight
\* if a client identifier is undefined then it is -1
NullHeight == -1
\* set of possible connection identifiers
ConnectionIds == 0..(MaxConnectionsPerChain- 1)
\* if a connection identifier is undefined then it is -1
NullConnectionId == -1
\* set of possible connection states
ConnectionStates == {
    "Uninit",
    "Init",
    "TryOpen",
    "Open"
}

\* mapping from client identifier to its height
Clients == [
    ClientIds -> ClientHeights \union {NullHeight}
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
ConnectionOpenInitActions == [
    type: {"ConnectionOpenInit"},
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
    "ICS02_OK",
    "ICS02_ClientNotFound",
    "ICS02_HeaderVerificationFailure",
    "ICS03_OK",
    "ICS03_MissingClient",
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

\* retrieves `connectionId`'s data
GetConnection(connections, connectionId) ==
    connections[connectionId]

\* check if a `connectionId` exists
ConnectionExists(connections, connectionId) ==
    GetConnection(connections, connectionId).state /= "Uninit"

\* update the `connectionId`'s data
SetConnection(connections, connectionId, connectionData) ==
    [connections EXCEPT ![connectionId] = connectionData]

CreateClient(chainId, clientHeight) ==
    LET chain == chains[chainId] IN
    LET clients == chain.clients IN
    LET clientIdCounter == chain.clientIdCounter IN
    \* check if the client exists (it shouldn't)
    IF ClientExists(clients, clientIdCounter) THEN
        \* if the client to be created already exists,
        \* then there's an error in the model
        /\ actionOutcome' = "ModelError"
        /\ UNCHANGED <<chains>>
    ELSE
        \* if it doesn't, create it
        LET updatedChain == [chain EXCEPT
            \* initialize the client's height to `clientHeight`
            !.clients = SetClientHeight(clients, clientIdCounter, clientHeight),
            \* update `clientIdCounter`
            !.clientIdCounter = clientIdCounter + 1
        ] IN
        \* update `chains` and set the outcome
        /\ chains' = [chains EXCEPT ![chainId] = updatedChain]
        /\ actionOutcome' = "ICS02_OK"

UpdateClient(chainId, clientId, clientHeight) ==
    LET chain == chains[chainId] IN
    LET clients == chain.clients IN
    \* check if the client exists
    IF ClientExists(clients, clientId) THEN
        \* if the client exists, check its height
        IF GetClientHeight(clients, clientId) < clientHeight THEN
            \* if the client's height is lower than the one being updated to
            \* then, update the client
            LET updatedChain == [chain EXCEPT
                \* set the client's height to `clientHeight`
                !.clients = SetClientHeight(clients, clientId, clientHeight)
            ] IN
            \* update `chains` and set the outcome
            /\ chains' = [chains EXCEPT ![chainId] = updatedChain]
            /\ actionOutcome' = "ICS02_OK"
        ELSE
            \* if the client's height is at least as high as the one being
            \* updated to, then set an error outcome
            /\ actionOutcome' = "ICS02_HeaderVerificationFailure"
            /\ UNCHANGED <<chains>>
    ELSE
        \* if the client does not exist, then set an error outcome
        /\ actionOutcome' = "ICS02_ClientNotFound"
        /\ UNCHANGED <<chains>>

ConnectionOpenInit(chainId, clientId, counterpartyClientId) ==
    LET chain == chains[chainId] IN
    LET clients == chain.clients IN
    LET connections == chain.connections IN
    LET connectionIdCounter == chain.connectionIdCounter IN
    \* check if the client exists
    IF ClientExists(clients, clientId) THEN
        \* if the client exists,
        \* then check if the connection exists (it shouldn't)
        IF ConnectionExists(connections, connectionIdCounter) THEN
            \* if the connection to be created already exists,
            \* then there's an error in the model
            /\ actionOutcome' = "ModelError"
            /\ UNCHANGED <<chains>>
        ELSE
            \* if it doesn't, create it
            LET connectionData == [
                state |-> "Init",
                clientId |-> clientId,
                counterpartyClientId |-> counterpartyClientId,
                connectionId |-> connectionIdCounter,
                counterpartyConnectionId |-> NullConnectionId
            ] IN
            LET updatedChain == [chain EXCEPT
                \* initialize the connection's data
                !.connections = SetConnection(connections, connectionIdCounter, connectionData),
                \* update `clientIdCounter`
                !.connectionIdCounter = connectionIdCounter + 1
            ] IN
            \* update `chains` and set the outcome
            /\ chains' = [chains EXCEPT ![chainId] = updatedChain]
            /\ actionOutcome' = "ICS03_OK"
    ELSE
        \* if the client does not exist, then set an error outcome
        /\ actionOutcome' = "ICS03_MissingClient"
        /\ UNCHANGED <<chains>>

CreateClientAction ==
    \* select a chain id
    \E chainId \in ChainIds:
    \* select a height for the client to be created at
    \E clientHeight \in ClientHeights:
        \* only create client if the model constant `MaxClientsPerChain` allows it
        /\ chains[chainId].clientIdCounter \in ClientIds
        /\ CreateClient(chainId, clientHeight)
        /\ action' = AsAction([type |-> "CreateClient",
                               chainId |-> chainId,
                               height |-> clientHeight])

UpdateClientAction ==
    \* select a chain id
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
        /\ action' = AsAction([type |-> "ConnectionOpenInit",
                               chainId |-> chainId,
                               clientId |-> clientId,
                               counterpartyClientId |-> counterpartyClientId])

Init ==
    \* create an empty chain
    LET emptyConnection == [
        state |-> "Uninit",
        clientId |-> NullClientId,
        counterpartyClientId |-> NullClientId,
        connectionId |-> NullConnectionId,
        counterpartyConnectionId |-> NullConnectionId
    ] IN
    LET emptyChain == [
        clients |-> [clientId \in ClientIds |-> NullHeight],
        clientIdCounter |-> 0,
        connections |-> [connectionId \in ConnectionIds |-> emptyConnection],
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
    /\ chains \in [ChainIds -> Chain]
    /\ action \in Actions
    /\ actionOutcome \in ActionOutcomes

\* the model never erros
ModelNeverErrors ==
    actionOutcome /= "ModelError"

=============================================================================
