------------------------------- MODULE ICS02 ----------------------------------

EXTENDS IBCDefinitions

\* retrieves `clientId`'s data
\* @type: (CLIENTS, CLIENT_ID) => CLIENT;
ICS02_GetClient(clients, clientId) ==
    clients[clientId]

\* check if `clientId` exists
\* @type: (CLIENTS, CLIENT_ID) => Bool;
ICS02_ClientExists(clients, clientId) ==
    ICS02_GetClient(clients, clientId).heights /= {}

\* update `clientId`'s data
\* @type: (CLIENTS, CLIENT_ID, CLIENT) => CLIENTS;
ICS02_SetClient(clients, clientId, client) ==
    [clients EXCEPT ![clientId] = client]

\* @type: (CHAIN, CHAIN_ID, HEIGHT) => [clients: CLIENTS, clientIdCounter: Int, action: ACTION, outcome: Str];
ICS02_CreateClient(chain, chainId, height) ==
    \* TODO: rename `action_` to `action` once the following issue is fixed:
    \*        https://github.com/informalsystems/apalache/issues/593
    LET action_ == [
        type |-> "Ics02CreateClient",
        chainId |-> chainId,
        clientState |-> height,
        consensusState |-> height
    ] IN
    \* check if the client exists (it shouldn't)
    IF ICS02_ClientExists(chain.clients, chain.clientIdCounter) THEN
        \* if the client to be created already exists,
        \* then there's an error in the model
        [
            clients |-> chain.clients,
            clientIdCounter |-> chain.clientIdCounter,
            action |-> action_,
            outcome |-> "ModelError"
        ]
    ELSE
        \* if it doesn't, create it
        LET client == [
            heights|-> {height}
        ] IN
        \* return result with updated state
        [
            clients |-> ICS02_SetClient(
                chain.clients,
                chain.clientIdCounter,
                client
            ),
            clientIdCounter |-> chain.clientIdCounter + 1,
            action |-> action_,
            outcome |-> "Ics02CreateOk"
        ]

\* @type: (CHAIN, CHAIN_ID, CLIENT_ID, HEIGHT) => [clients: CLIENTS, action: ACTION, outcome: Str];
ICS02_UpdateClient(chain, chainId, clientId, height) ==
    LET action_ == [
        type |-> "Ics02UpdateClient",
        chainId |-> chainId,
        clientId |-> clientId,
        header |-> height
    ] IN
    \* check if the client exists
    IF ~ICS02_ClientExists(chain.clients, clientId) THEN
        \* if the client does not exist, then set an error outcome
        [
            clients |-> chain.clients,
            action |-> action_,
            outcome |-> "Ics02ClientNotFound"
        ]
    ELSE
        \* if the client exists, check its height
        LET client == ICS02_GetClient(chain.clients, clientId) IN
        LET highestHeight == FindMaxHeight(client.heights) IN
        IF ~HigherRevisionHeight(height, highestHeight) THEN
            \* if the client's new height is not at the same revision number and a higher
            \* block height than the highest client height, then set an error outcome
            [
                clients |-> chain.clients,
                action |-> action_,
                outcome |-> "Ics02HeaderVerificationFailure"
            ]
        ELSE
            \* if the client's new height is higher than the highest client
            \* height, then update the client
            LET updatedClient == [client EXCEPT
                !.heights = client.heights \union {height}
            ] IN
            \* return result with updated state
            [
                clients |-> ICS02_SetClient(
                    chain.clients,
                    clientId,
                    updatedClient
                ),
                action |-> action_,
                outcome |-> "Ics02UpdateOk"
            ]

\* @type: (CHAIN, CHAIN_ID, CLIENT_ID, HEIGHT) => [clients: CLIENTS, action: ACTION, outcome: Str];
ICS07_UpgradeClient(chain, chainId, clientId, height) ==
    LET action_ == [
        type |-> "Ics07UpgradeClient",
        chainId |-> chainId,
        clientId |-> clientId,
        header |-> height
    ] IN
    \* check if the client exists
    IF ~ICS02_ClientExists(chain.clients, clientId) THEN
        \* if the client does not exist, then set an error outcome
        [
            clients |-> chain.clients,
            action |-> action_,
            outcome |-> "Ics07ClientNotFound"
        ]
    ELSE
        \* if the client exists, check its height
        LET client == ICS02_GetClient(chain.clients, clientId) IN
        LET highestHeight == FindMaxHeight(client.heights) IN
        IF ~HigherRevisionNumber(height, highestHeight) THEN
            \* if the client's new height is not at a higher revision than the highest client
            \* height, then set an error outcome
            [
                clients |-> chain.clients,
                action |-> action_,
                outcome |-> "Ics07HeaderVerificationFailure"
            ]
        ELSE
            \* if the client's new height is higher than the highest client
            \* height, then update the client
            LET updatedClient == [client EXCEPT
                !.heights = client.heights \union {height}
            ] IN
            \* return result with updated state
            [
                clients |-> ICS02_SetClient(
                    chain.clients,
                    clientId,
                    updatedClient
                ),
                action |-> action_,
                outcome |-> "Ics07UpgradeOk"
            ]

===============================================================================
