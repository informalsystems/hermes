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

\* retrieves `clientId`'s data
GetClient(clients, clientId) ==
    clients[clientId]

\* check if `clientId` exists
ClientExists(clients, clientId) ==
    GetClient(clients, clientId).height /= NullHeight

\* update `clientId`'s data
SetClient(clients, clientId, client) ==
    [clients EXCEPT ![clientId] = client]

\* retrieves `connectionId`'s data
GetConnection(connections, connectionId) ==
    connections[connectionId]

\* check if `connectionId` exists
ConnectionExists(connections, connectionId) ==
    GetConnection(connections, connectionId).state /= "Uninit"

\* update `connectionId`'s data
SetConnection(connections, connectionId, connection) ==
    [connections EXCEPT ![connectionId] = connection]

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
        LET client == [
            height |-> clientHeight
        ] IN
        \* update the chain
        LET updatedChain == [chain EXCEPT
            !.clients = SetClient(clients, clientIdCounter, client),
            !.clientIdCounter = clientIdCounter + 1
        ] IN
        \* update `chains` and set the outcome
        /\ chains' = [chains EXCEPT ![chainId] = updatedChain]
        /\ actionOutcome' = "ICS02CreateOK"

UpdateClient(chainId, clientId, clientHeight) ==
    LET chain == chains[chainId] IN
    LET clients == chain.clients IN
    \* check if the client exists
    IF ClientExists(clients, clientId) THEN
        \* if the client exists, check its height
        LET client == GetClient(clients, clientId) IN
        IF client.height < clientHeight THEN
            \* if the client's height is lower than the one being updated to
            \* then, update the client
            LET updatedClient == [client EXCEPT
                !.height = clientHeight
            ] IN
            \* update the chain
            LET updatedChain == [chain EXCEPT
                !.clients = SetClient(clients, clientId, updatedClient)
            ] IN
            \* update `chains` and set the outcome
            /\ chains' = [chains EXCEPT ![chainId] = updatedChain]
            /\ actionOutcome' = "ICS02UpdateOK"
        ELSE
            \* if the client's height is at least as high as the one being
            \* updated to, then set an error outcome
            /\ actionOutcome' = "ICS02HeaderVerificationFailure"
            /\ UNCHANGED <<chains>>
    ELSE
        \* if the client does not exist, then set an error outcome
        /\ actionOutcome' = "ICS02ClientNotFound"
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
            LET connection == [
                state |-> "Init",
                clientId |-> clientId,
                counterpartyClientId |-> counterpartyClientId,
                connectionId |-> connectionIdCounter,
                counterpartyConnectionId |-> NullConnectionId
            ] IN
            \* update the chain
            LET updatedChain == [chain EXCEPT
                !.connections = SetConnection(connections, connectionIdCounter, connection),
                !.connectionIdCounter = connectionIdCounter + 1
            ] IN
            \* update `chains` and set the outcome
            /\ chains' = [chains EXCEPT ![chainId] = updatedChain]
            /\ actionOutcome' = "ICS03ConnectionOpenInitOK"
    ELSE
        \* if the client does not exist, then set an error outcome
        /\ actionOutcome' = "ICS03MissingClient"
        /\ UNCHANGED <<chains>>

CreateClientAction ==
    \* select a chain id
    \E chainId \in ChainIds:
    \* select a height for the client to be created at
    \E clientHeight \in ClientHeights:
        \* only create client if the model constant `MaxClientsPerChain` allows it
        /\ chains[chainId].clientIdCounter \in ClientIds
        /\ CreateClient(chainId, clientHeight)
        /\ action' = AsAction([type |-> "ICS02CreateClient",
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
        /\ action' = AsAction([type |-> "ICS02UpdateClient",
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
        /\ action' = AsAction([type |-> "ICS03ConnectionOpenInit",
                               chainId |-> chainId,
                               clientId |-> clientId,
                               counterpartyClientId |-> counterpartyClientId])

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
