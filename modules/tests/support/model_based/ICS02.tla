------------------------------- MODULE ICS02 ----------------------------------

EXTENDS Integers, FiniteSets, IBCDefinitions

\* retrieves `clientId`'s data
ICS02_GetClient(clients, clientId) ==
    clients[clientId]

\* check if `clientId` exists
ICS02_ClientExists(clients, clientId) ==
    ICS02_GetClient(clients, clientId).heights /= AsSetInt({})

\* update `clientId`'s data
ICS02_SetClient(clients, clientId, client) ==
    [clients EXCEPT ![clientId] = client]

ICS02_CreateClient(chain, chainId, height) ==
    LET action == AsAction([
        type |-> "ICS02CreateClient",
        chainId |-> chainId,
        clientState |-> height,
        consensusState |-> height
    ]) IN
    LET clients == chain.clients IN
    LET clientIdCounter == chain.clientIdCounter IN
    \* check if the client exists (it shouldn't)
    IF ICS02_ClientExists(clients, clientIdCounter) THEN
        \* if the client to be created already exists,
        \* then there's an error in the model
        [
            clients |-> clients,
            clientIdCounter |-> clientIdCounter,
            action |-> action,
            outcome |-> "ModelError"
        ]
    ELSE
        \* if it doesn't, create it
        LET client == [
            heights|-> {height}
        ] IN
        \* return result with updated state
        [
            clients |-> ICS02_SetClient(clients, clientIdCounter, client),
            clientIdCounter |-> clientIdCounter + 1,
            action |-> action,
            outcome |-> "ICS02CreateOK"
        ]

ICS02_UpdateClient(chain, chainId, clientId, height) ==
    LET action == AsAction([
        type |-> "ICS02UpdateClient",
        chainId |-> chainId,
        clientId |-> clientId,
        header |-> height
    ]) IN
    LET clients == chain.clients IN
    \* check if the client exists
    IF ICS02_ClientExists(clients, clientId) THEN
        \* if the client exists, check its height
        LET client == ICS02_GetClient(clients, clientId) IN
        LET latestHeight == Max(client.heights) IN
        IF latestHeight < height THEN
            \* if the client's height is lower than the one being updated to
            \* then, update the client
            LET updatedClient == [client EXCEPT
                !.heights = client.heights \union {height}
            ] IN
            \* return result with updated state
            [
                clients |-> ICS02_SetClient(clients, clientId, updatedClient),
                action |-> action,
                outcome |-> "ICS02UpdateOK"
            ]
        ELSE
            \* if the client's height is at least as high as the one being
            \* updated to, then set an error outcome
            [
                clients |-> clients,
                action |-> action,
                outcome |-> "ICS02HeaderVerificationFailure"
            ]
    ELSE
        \* if the client does not exist, then set an error outcome
        [
            clients |-> clients,
            action |-> action,
            outcome |-> "ICS02ClientNotFound"
        ]

===============================================================================
