------------------------------- MODULE ICS02 ----------------------------------

EXTENDS Integers, FiniteSets, IBCDefinitions

\* retrieves `clientId`'s data
ICS02_GetClient(clients, clientId) ==
    clients[clientId]

\* check if `clientId` exists
ICS02_ClientExists(clients, clientId) ==
    ICS02_GetClient(clients, clientId).height /= HeightNone

\* update `clientId`'s data
ICS02_SetClient(clients, clientId, client) ==
    [clients EXCEPT ![clientId] = client]

ICS02_CreateClient(clients, clientIdCounter, clientHeight) ==
    \* check if the client exists (it shouldn't)
    IF ICS02_ClientExists(clients, clientIdCounter) THEN
        \* if the client to be created already exists,
        \* then there's an error in the model
        [
            clients |-> clients,
            clientIdCounter |-> clientIdCounter,
            outcome |-> "ModelError"
        ]
    ELSE
        \* if it doesn't, create it
        LET client == [
            height |-> clientHeight
        ] IN
        \* return result with updated state
        [
            clients |-> ICS02_SetClient(clients, clientIdCounter, client),
            clientIdCounter |-> clientIdCounter + 1,
            outcome |-> "ICS02CreateOK"
        ]

ICS02_UpdateClient(clients, clientId, clientHeight) ==
    \* check if the client exists
    IF ICS02_ClientExists(clients, clientId) THEN
        \* if the client exists, check its height
        LET client == ICS02_GetClient(clients, clientId) IN
        IF client.height < clientHeight THEN
            \* if the client's height is lower than the one being updated to
            \* then, update the client
            LET updatedClient == [client EXCEPT
                !.height = clientHeight
            ] IN
            \* return result with updated state
            [
                clients |-> ICS02_SetClient(clients, clientId, updatedClient),
                outcome |-> "ICS02UpdateOK"
            ]
        ELSE
            \* if the client's height is at least as high as the one being
            \* updated to, then set an error outcome
            [
                clients |-> clients,
                outcome |-> "ICS02HeaderVerificationFailure"
            ]
    ELSE
        \* if the client does not exist, then set an error outcome
        [
            clients |-> clients,
            outcome |-> "ICS02ClientNotFound"
        ]
        \* TODO: distinguish between client state and consensus state to also be
        \*       able to return a `ConsensusStateNotFound` error outcome

===============================================================================
