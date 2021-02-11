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
    clients,
    connections,
    connectionIdCounter,
    clientId,
    counterpartyClientId
) ==
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
                outcome |-> "ICS03ConnectionOpenInitOK"
            ]
    ELSE
        \* if the client does not exist, then set an error outcome
        [
            connections |-> connections,
            connectionIdCounter |-> connectionIdCounter,
            outcome |-> "ICS03MissingClient"
        ]

\* TODO: errors generated when verifying proofs are never an outcome of this
\*       model
ICS03_ConnectionOpenTry(
    chainHeight,
    clients,
    connections,
    connectionIdCounter,
    previousConnectionId,
    clientId,
    height,
    counterpartyClientId,
    counterpartyConnectionId
) ==
    \* check if client's claimed height is higher than the chain's height
    IF height > chainHeight THEN
        \* if client's height is too advanced, then set an error outcome
        [
            connections |-> connections,
            connectionIdCounter |-> connectionIdCounter,
            outcome |-> "ICS03InvalidConsensusHeight"
        ]
        \* TODO: add `chain_max_history_size` to the model to be able to also
        \*       return a `ICS03StaleConsensusHeight` error outcome
    ELSE
        \* check if there's a `previousConnectionId`
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
                THEN
                    \* verification passed; update connection
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
                        outcome |-> "ICS03ConnectionOpenTryOK"
                    ]
                ELSE
                    [
                        connections |-> connections,
                        connectionIdCounter |-> connectionIdCounter,
                        outcome |-> "ICS03ConnectionMismatch"
                    ]
            ELSE
                \* if the connection does not exist, then set an error outcome
                [
                    connections |-> connections,
                    connectionIdCounter |-> connectionIdCounter,
                    outcome |-> "ICS03ConnectionNotFound"
                ]
        ELSE
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
                outcome |-> "ICS03ConnectionOpenTryOK"
            ]

===============================================================================
