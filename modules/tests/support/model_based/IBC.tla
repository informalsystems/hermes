--------------------------------- MODULE IBC ----------------------------------

EXTENDS Integers, FiniteSets, ICS02, ICS03

\* ids of existing chains
CONSTANT ChainIds
\* max height which chains can reach
CONSTANT MaxChainHeight
ASSUME MaxChainHeight >= 0
\* max number of client to be created per chain
CONSTANT MaxClientsPerChain
ASSUME MaxClientsPerChain >= 0
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

\* set of possible chain heights
Heights == 1..MaxChainHeight
\* set of possible client identifiers
ClientIds == 0..(MaxClientsPerChain - 1)
\* set of possible connection identifiers
ConnectionIds == 0..(MaxConnectionsPerChain- 1)
\* set of possible connection states
ConnectionStates == {
    "Uninit",
    "Init",
    "TryOpen",
    "Open"
}

\* set of possible actions
NoneActions == [
    type: {"None"}
] <: {ActionType}

CreateClientActions == [
    type: {"ICS02CreateClient"},
    chainId: ChainIds,
    \* client state contains simply a height
    clientState: Heights,
    \* consensus state contains simply a height
    consensusState: Heights
] <: {ActionType}
UpdateClientActions == [
    type: {"ICS02UpdateClient"},
    chainId: ChainIds,
    clientId: ClientIds,
    \* header contains simply a height
    header: Heights
] <: {ActionType}
ClientActions ==
    CreateClientActions \union
    UpdateClientActions

ConnectionOpenInitActions == [
    type: {"ICS03ConnectionOpenInit"},
    chainId: ChainIds,
    clientId: ClientIds,
    counterpartyClientId: ClientIds
] <: {ActionType}
ConnectionOpenTryActions == [
    type: {"ICS03ConnectionOpenTry"},
    chainId: ChainIds,
    clientId: ClientIds,
    \* `previousConnectionId` can be none
    previousConnectionId: ConnectionIds \union {ConnectionIdNone},
    \* client state contains simply a height
    clientState: Heights,
    counterpartyChainId: ChainIds,
    counterpartyClientId: ClientIds,
    counterpartyConnectionId: ConnectionIds
] <: {ActionType}
ConnectionActions ==
    ConnectionOpenInitActions \union
    ConnectionOpenTryActions

Actions ==
    NoneActions \union
    ClientActions \union
    ConnectionActions

\* set of possible action outcomes
ActionOutcomes == {
    "None",
    "ModelError",
    \* ICS02_CreateClient outcomes:
    "ICS02CreateOK",
    \* ICS02_UpdateClient outcomes:
    "ICS02UpdateOK",
    "ICS02ClientNotFound",
    "ICS02HeaderVerificationFailure",
    \* ICS03_ConnectionOpenInit outcomes:
    "ICS03ConnectionOpenInitOK",
    "ICS03MissingClient",
    \* ICS03_ConnectionOpenTry outcomes:
    "ICS03ConnectionOpenTryOK",
    "ICS03InvalidConsensusHeight",
    "ICS03ConnectionNotFound",
    "ICS03ConnectionMismatch"
}

\* data kept per client
Client == [
    heights: SUBSET Heights
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
    height: Heights,
    clients: Clients,
    clientIdCounter: 0..MaxClientsPerChain,
    connections: Connections,
    connectionIdCounter: 0..MaxConnectionsPerChain,
    connectionProofs: SUBSET ConnectionActions
]
\* mapping from chain identifier to its data
Chains == [
    ChainIds -> Chain
]

(***************************** Specification *********************************)

\* update chain height if outcome was ok
UpdateChainHeight(height, outcome, okOutcome) ==
    IF outcome = okOutcome THEN height + 1 ELSE height

CreateClient(chainId, height) ==
    LET chain == chains[chainId] IN
    LET result == ICS02_CreateClient(chain, height) IN
    LET newAction == AsAction([
        type |-> "ICS02CreateClient",
        chainId |-> chainId,
        clientState |-> height,
        consensusState |-> height
    ]) IN
    \* update the chain
    LET updatedChain == [chain EXCEPT
        !.height = UpdateChainHeight(@, result.outcome, "ICS02CreateOK"),
        !.clients = result.clients,
        !.clientIdCounter = result.clientIdCounter
    ] IN
    \* update `chains`, set the `action` and its `actionOutcome`
    /\ chains' = [chains EXCEPT ![chainId] = updatedChain]
    /\ action' = newAction
    /\ actionOutcome' = result.outcome

UpdateClient(chainId, clientId, height) ==
    LET chain == chains[chainId] IN
    LET result == ICS02_UpdateClient(chain, clientId, height) IN
    LET newAction == AsAction([
        type |-> "ICS02UpdateClient",
        chainId |-> chainId,
        clientId |-> clientId,
        header |-> height
    ]) IN
    \* update the chain
    LET updatedChain == [chain EXCEPT
        !.height = UpdateChainHeight(@, result.outcome, "ICS03CreateOK"),
        !.clients = result.clients
    ] IN
    \* update `chains`, set the `action` and its `actionOutcome`
    /\ chains' = [chains EXCEPT ![chainId] = updatedChain]
    /\ action' = newAction
    /\ actionOutcome' = result.outcome

ConnectionOpenInit(chainId, clientId, counterpartyClientId) ==
    LET chain == chains[chainId] IN
    LET result == ICS03_ConnectionOpenInit(
        chain,
        clientId,
        counterpartyClientId
    ) IN
    LET newAction == AsAction([
        type |-> "ICS03ConnectionOpenInit",
        chainId |-> chainId,
        clientId |-> clientId,
        counterpartyClientId |-> counterpartyClientId
    ]) IN
    \* update the chain
    LET updatedChain == [chain EXCEPT
        !.height = UpdateChainHeight(@, result.outcome, "ICS03ConnectionOpenInitOK"),
        !.connections = result.connections,
        !.connectionIdCounter = result.connectionIdCounter
    ] IN
    \* update `chains`, set the `action` and its `actionOutcome`
    /\ chains' = [chains EXCEPT ![chainId] = updatedChain]
    /\ action' = newAction
    /\ actionOutcome' = result.outcome

ConnectionOpenTry(
    chainId,
    clientId,
    previousConnectionId,
    height,
    counterpartyChainId,
    counterpartyClientId,
    counterpartyConnectionId
) ==
    LET chain == chains[chainId] IN
    \* pass all the `chains` so that the model can check that the open try is
    \* valid (i.e. there has been an open init on the counterparty chain);
    \* the implementation uses proofs for this
    LET result == ICS03_ConnectionOpenTry(
        chain,
        clientId,
        previousConnectionId,
        height,
        counterpartyChainId,
        counterpartyClientId,
        counterpartyConnectionId
    ) IN
    LET newAction == AsAction([
        type |-> "ICS03ConnectionOpenTry",
        chainId |-> chainId,
        clientId |-> clientId,
        previousConnectionId |-> previousConnectionId,
        clientState |-> height,
        counterpartyChainId |-> counterpartyChainId,
        counterpartyClientId |-> counterpartyClientId,
        counterpartyConnectionId |-> counterpartyConnectionId
    ]) IN
    \* update the chain
    LET updatedChain == [chain EXCEPT
        !.height = UpdateChainHeight(@, result.outcome, "ICS03ConnectionOpenTryOK"),
        !.connections = result.connections,
        !.connectionIdCounter = result.connectionIdCounter
    ] IN
    \* update `chains`, set the `action` and its `actionOutcome`
    /\ chains' = [chains EXCEPT ![chainId] = updatedChain]
    /\ action' = newAction
    /\ actionOutcome' = result.outcome

CreateClientAction(chainId) ==
    \* select a height for the client to be created at
    \E height \in Heights:
        \* only create client if the model constant `MaxClientsPerChain` allows
        \* it
        IF chains[chainId].clientIdCounter < MaxClientsPerChain THEN
            CreateClient(chainId, height)
        ELSE
            UNCHANGED vars

UpdateClientAction(chainId) ==
    \* select a client to be updated (which may not exist)
    \E clientId \in ClientIds:
    \* select a height for the client to be updated
    \E height \in Heights:
        UpdateClient(chainId, clientId, height)

ConnectionOpenInitAction(chainId) ==
    \* select a client id
    \E clientId \in ClientIds:
    \* select a counterparty client id
    \E counterpartyClientId \in ClientIds:
        \* only create connection if the model constant `MaxConnectionsPerChain`
        \* allows it
        IF chains[chainId].connectionIdCounter < MaxConnectionsPerChain THEN
            ConnectionOpenInit(chainId, clientId, counterpartyClientId)
        ELSE
            UNCHANGED vars

ConnectionOpenTryAction(chainId) ==
    \* select a client id
    \E clientId \in ClientIds:
    \* select a previous connection id (which can be none)
    \E previousConnectionId \in ConnectionIds \union {ConnectionIdNone}:
    \* select a claimed height for the client
    \E height \in Heights:
    \* select a counterparty chain id
    \E counterpartyChainId \in ChainIds:
    \* select a counterparty client id
    \E counterpartyClientId \in ClientIds:
    \* select a counterparty connection id
    \E counterpartyConnectionId \in ConnectionIds:
        \* only perform action if there was a previous connection or if the
        \* model constant `MaxConnectionsPerChain` allows that a new connection
        \* is created
        IF \/ previousConnectionId /= ConnectionIdNone
           \/ chains[chainId].connectionIdCounter < MaxConnectionsPerChain THEN
            ConnectionOpenTry(
                chainId,
                clientId,
                previousConnectionId,
                height,
                counterpartyChainId,
                counterpartyClientId,
                counterpartyConnectionId
            )
        ELSE
            UNCHANGED vars

Init ==
    \* create a client and a connection with none values
    LET clientNone == [
        heights |-> AsSetInt({})
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
        height |-> 1,
        clients |-> [clientId \in ClientIds |-> clientNone],
        clientIdCounter |-> 0,
        connections |-> [connectionId \in ConnectionIds |-> connectionNone],
        connectionIdCounter |-> 0,
        connectionProofs |-> AsSetAction({})
    ] IN
    /\ chains = [chainId \in ChainIds |-> emptyChain]
    /\ action = AsAction([type |-> "None"])
    /\ actionOutcome = "None"

Next ==
    \* select a chain id
    \E chainId \in ChainIds:
        \* perform action on chain if the model constant `MaxChainHeight` allows
        \* it
        IF chains[chainId].height < MaxChainHeight THEN
            \/ CreateClientAction(chainId)
            \/ UpdateClientAction(chainId)
            \/ ConnectionOpenInitAction(chainId)
            \/ ConnectionOpenTryAction(chainId)
            \/ UNCHANGED vars
        ELSE
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
