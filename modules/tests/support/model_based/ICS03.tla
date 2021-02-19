------------------------------ MODULE ICS03 -----------------------------------

EXTENDS Integers, FiniteSets, IBCDefinitions, ICS02

\* retrieves `connectionId`'s data
ICS03_GetConnection(connections, connectionId) ==
    connections[connectionId]

\* check if `connectionId` exists
ICS03_ConnectionExists(connections, connectionId) ==
    ICS03_GetConnection(connections, connectionId).state /= "Uninit"

\* update `connectionId`'s data
ICS03_SetConnection(connections, connectionId, connection) ==
    [connections EXCEPT ![connectionId] = connection]

ICS03_ConnectionOpenInit(
    chain,
    chainId,
    clientId,
    counterpartyChainId,
    counterpartyClientId
) ==
    LET action == AsAction([
        type |-> "ICS03ConnectionOpenInit",
        chainId |-> chainId,
        clientId |-> clientId,
        counterpartyChainId |-> counterpartyChainId,
        counterpartyClientId |-> counterpartyClientId
    ]) IN
    LET clients == chain.clients IN
    LET connections == chain.connections IN
    LET connectionIdCounter == chain.connectionIdCounter IN
    \* check if the client exists
    IF ICS02_ClientExists(clients, clientId) THEN
        \* if the client exists,
        \* then check if the connection exists (it shouldn't)
        IF ICS03_ConnectionExists(connections, connectionIdCounter) THEN
            \* if the connection to be created already exists,
            \* then there's an error in the model
            [
                connections |-> connections,
                connectionIdCounter |-> connectionIdCounter,
                action |-> action,
                outcome |-> "ModelError"
            ]
        ELSE
            \* if it doesn't, create it
            LET connection == [
                state |-> "Init",
                clientId |-> clientId,
                counterpartyClientId |-> counterpartyClientId,
                connectionId |-> connectionIdCounter,
                counterpartyConnectionId |-> ConnectionIdNone
            ] IN
            \* return result with updated state
            [
                connections |-> ICS03_SetConnection(
                    connections,
                    connectionIdCounter,
                    connection
                ),
                connectionIdCounter |-> connectionIdCounter + 1,
                action |-> action,
                outcome |-> "ICS03ConnectionOpenInitOK"
            ]
    ELSE
        \* if the client does not exist, then set an error outcome
        [
            connections |-> connections,
            connectionIdCounter |-> connectionIdCounter,
            action |-> action,
            outcome |-> "ICS03MissingClient"
        ]

\* TODO: errors generated when verifying proofs are never an outcome of this
\*       model
\* TODO: check for a missing client?
ICS03_ConnectionOpenTry(
    chain,
    chainId,
    clientId,
    previousConnectionId,
    height,
    counterpartyChainId,
    counterpartyClientId,
    counterpartyConnectionId
) ==
    LET action == AsAction([
        type |-> "ICS03ConnectionOpenTry",
        chainId |-> chainId,
        clientId |-> clientId,
        previousConnectionId |-> previousConnectionId,
        clientState |-> height,
        counterpartyChainId |-> counterpartyChainId,
        counterpartyClientId |-> counterpartyClientId,
        counterpartyConnectionId |-> counterpartyConnectionId
    ]) IN
    LET clients == chain.clients IN
    LET connections == chain.connections IN
    LET connectionIdCounter == chain.connectionIdCounter IN
    LET connectionProofs == chain.connectionProofs IN
    \* check if client's claimed height is higher than the chain's height
    IF height > chain.height THEN
        \* if client's height is too advanced, then set an error outcome
        \* TODO: in the ICS03, this error also occurs if
        \*       "height == chain.height", which is not the case in the
        \*       Rust implementation
        [
            connections |-> connections,
            connectionIdCounter |-> connectionIdCounter,
            action |-> action,
            outcome |-> "ICS03InvalidConsensusHeight"
        ]
        \* TODO: add `chain_max_history_size` to the model to be able to also
        \*       return a `ICS03StaleConsensusHeight` error outcome
    ELSE
        \* check if there's a `previousConnectionId`. this situation can happen
        \* where there are two concurrent open init's establishing a connection
        \* between the same two chains, say chainA and chainB; then, when chainB
        \* sees the open init from chainA, instead of creating a new connection
        \* identifier, it can reuse the identifier created by its own open init.
        IF previousConnectionId /= ConnectionIdNone THEN
            \* if so, check if the connection exists
            IF ICS03_ConnectionExists(connections, previousConnectionId) THEN
                \* if the connection exists, verify that is matches the
                \* the parameters provided
                LET connection == ICS03_GetConnection(
                    connections,
                    previousConnectionId
                ) IN
                IF /\ connection.state = "Init"
                   /\ connection.clientId = clientId
                   /\ connection.counterpartyClientId = counterpartyClientId
                   /\ connection.counterpartyConnectionId = counterpartyConnectionId
                THEN
                    \* verification passed; update the connection state to
                    \* "TryOpen"
                    LET updatedConnection == [
                        state |-> "TryOpen",
                        clientId |-> clientId,
                        connectionId |-> previousConnectionId,
                        counterpartyClientId |-> counterpartyClientId,
                        counterpartyConnectionId |-> counterpartyConnectionId
                    ] IN
                    \* return result with updated state
                    [
                        connections |-> ICS03_SetConnection(
                            connections,
                            previousConnectionId,
                            updatedConnection
                        ),
                        \* as the connection identifier has already been
                        \* created, here we do not update the
                        \* `connectionIdCounter`
                        connectionIdCounter |-> connectionIdCounter,
                        action |-> action,
                        outcome |-> "ICS03ConnectionOpenTryOK"
                    ]
                ELSE
                    [
                        connections |-> connections,
                        connectionIdCounter |-> connectionIdCounter,
                        action |-> action,
                        outcome |-> "ICS03ConnectionMismatch"
                    ]
            ELSE
                \* if the connection does not exist, then set an error outcome
                [
                    connections |-> connections,
                    connectionIdCounter |-> connectionIdCounter,
                    action |-> action,
                    outcome |-> "ICS03ConnectionNotFound"
                ]
        ELSE
            \* check if there was an open init at the remote chain
            LET openInitProofs == {
                proof \in chain.connectionProofs :
                    /\ proof.type = "ICS03ConnectionOpenInit"
                    /\ chainId = counterpartyChainId
                    /\ clientId = counterpartyClientId
                    /\ counterpartyChainId = chainId
                    /\ counterpartyClientId = clientId
            } IN
            IF Cardinality(openInitProofs) > 0 THEN
                \* verification passed; create connection
                LET connection == [
                    state |-> "TryOpen",
                    clientId |-> clientId,
                    \* generate a new connection identifier
                    connectionId |-> connectionIdCounter,
                    counterpartyClientId |-> counterpartyClientId,
                    counterpartyConnectionId |-> counterpartyConnectionId
                ] IN
                \* return result with updated state
                [
                    connections |-> ICS03_SetConnection(
                        connections,
                        connectionIdCounter,
                        connection
                    ),
                    \* since a new connection identifier has been created, here we
                    \* update the `connectionIdCounter`
                    connectionIdCounter |-> connectionIdCounter + 1,
                    action |-> action,
                    outcome |-> "ICS03ConnectionOpenTryOK"
                ]
            ELSE
                [
                    connections |-> connections,
                    connectionIdCounter |-> connectionIdCounter,
                    action |-> action,
                    outcome |-> "ICS03InvalidProof"
                ]

===============================================================================
