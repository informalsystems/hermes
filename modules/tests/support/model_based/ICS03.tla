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
                counterpartyConnectionId |-> NullConnectionId
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

===============================================================================