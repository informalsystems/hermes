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

ICS03_ConnectionOpenTry_1(
    chainHeight,
    clients,
    connections,
    connectionIdCounter,
    clientId,
    clientClaimedHeight,
    counterpartyClientId,
    connectionId
) ==
    \* TODO check that all parameters are still needed
    [
        connections |-> connections,
        connectionIdCounter |-> connectionIdCounter,
        outcome |-> "ICS03ConnectionOpenTryOK"
    ]

ICS03_ConnectionOpenTry_0(
    chainHeight,
    clients,
    connections,
    connectionIdCounter,
    clientId,
    clientClaimedHeight,
    counterpartyClientId,
    connectionId
) ==
    \* check if client's claimed height is higher than the chain's height
    IF clientClaimedHeight > chainHeight THEN
        \* if client's height is too advanced, then set an error outcome
        [
            connections |-> connections,
            connectionIdCounter |-> connectionIdCounter,
            outcome |-> "ICS03InvalidConsensusHeight"
        ]
        \* TODO: add `chain_max_history_size` to the model to be able to also
        \*       return a `ICS03StaleConsensusHeight` error outcome
    ELSE
        \* check if a `connectionId` was set
        IF connectionId /= ConnectionIdNone THEN
            \* if so, check if the connection exists
            IF ICS03_ConnectionExists(connections, connectionId) THEN
                \* if the connection exists, verify that is matches the
                \* the parameters provided
                LET connection == ICS03_GetConnection(
                    connections,
                    connectionId
                ) IN
                IF /\ connection.state = "Init"
                   /\ connection.clientId = clientId
                   /\ connection.counterpartyClientId = counterpartyClientId
                THEN
                    \* initial verification passed; move to step 1
                    ICS03_ConnectionOpenTry_1(
                        chainHeight,
                        clients,
                        connections,
                        connectionIdCounter,
                        clientId,
                        clientClaimedHeight,
                        counterpartyClientId,
                        connectionId
                    )
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
            \* initial verification passed; move to step 1
            ICS03_ConnectionOpenTry_1(
                chainHeight,
                clients,
                connections,
                connectionIdCounter,
                clientId,
                clientClaimedHeight,
                counterpartyClientId,
                connectionId
            )

ICS03_ConnectionOpenTry(
    chainHeight,
    clients,
    connections,
    connectionIdCounter,
    clientId,
    clientClaimedHeight,
    counterpartyClientId,
    connectionId
) ==
    \* start step 0
    ICS03_ConnectionOpenTry_0(
        chainHeight,
        clients,
        connections,
        connectionIdCounter,
        clientId,
        clientClaimedHeight,
        counterpartyClientId,
        connectionId
    )

===============================================================================