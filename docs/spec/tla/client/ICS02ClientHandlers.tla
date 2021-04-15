----------------------- MODULE ICS02ClientHandlers -------------------------

(***************************************************************************
 This module contains definitions of operators that are used to handle
 client create and update datagrams.
 ***************************************************************************)

EXTENDS Integers, FiniteSets, ICS02Definitions

(***************************************************************************
 Client datagram handlers
 ***************************************************************************)
    
\* Handle "CreateClient" datagrams
\* @type: (CHAINSTORE, Str, Set(DATAGRAM)) => CHAINSTORE;
HandleCreateClient(chain, clientID, datagrams) == 
    \* get "CreateClient" datagrams with valid clientID
    LET createClientDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "CreateClient"
                            /\ dgr.clientID = clientID} IN
    \* get heights in datagrams with correct counterparty clientID for chainID
    LET createClientHeights == {dgr.height : dgr \in createClientDgrs} IN  
    \* get next available client number where a client can be created  
    LET nextClientNr == 
            IF /\ \A clientNr \in DOMAIN chain.clientStates :
                    chain.clientStates[clientNr].clientID /= clientID
               /\ \E clientNr \in DOMAIN chain.clientStates :  
                    chain.clientStates[clientNr].clientID = nullClientID
            THEN CHOOSE clientNr \in DOMAIN chain.clientStates :
                    \/ /\ clientNr = 1
                       /\ chain.clientStates[clientNr].clientID = nullClientID
                    \/ /\ clientNr - 1 \in DOMAIN chain.clientStates
                       /\ chain.clientStates[clientNr - 1].clientID /= nullClientID
                       /\ chain.clientStates[clientNr].clientID = nullClientID
            ELSE 0 IN
                            
    \* new chain record with client created
    LET clientCreateChain == 
        IF nextClientNr \in DOMAIN chain.clientStates 
        THEN [chain EXCEPT !.clientStates = 
                [chain.clientStates EXCEPT ![nextClientNr] =
                    \* if the slot at nextClientNr is an empty slot
                    IF /\ chain.clientStates[nextClientNr].clientID = nullClientID
                    \* if the set of heights from datagrams is not empty
                       /\ createClientHeights /= {}
                    \* then create a client with clientID at the slot nextClientNr
                    THEN [clientID |-> clientID, 
                          heights |-> {Max(createClientHeights)}]
                    \* otherwise, discard CreateClient datagrams  
                    ELSE chain.clientStates[nextClientNr]
             ]]
        ELSE chain IN
                       
    clientCreateChain

\* Handle "ClientUpdate" datagrams
\* @type: (CHAINSTORE, Str, Set(DATAGRAM), Int) => CHAINSTORE;
HandleClientUpdate(chain, clientID, datagrams, MaxHeight) ==     
    \* get the client number of the client with clientID
    LET clientNr == IF \E clientNr \in DOMAIN chain.clientStates : 
                        chain.clientStates[clientNr].clientID = clientID
                    THEN CHOOSE clientNr \in DOMAIN chain.clientStates : 
                            chain.clientStates[clientNr].clientID = clientID 
                    ELSE 0 IN
    \* max client height of client ID
    LET maxClientHeight == IF clientNr /= 0
                           THEN Max(chain.clientStates[clientNr].heights)
                           ELSE MaxHeight IN 
    \* get "ClientUpdate" datagrams with valid clientID
    LET updateClientDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ClientUpdate"
                            /\ dgr.clientID = clientID
                            /\ maxClientHeight < dgr.height} IN
    \* get heights in datagrams with correct counterparty clientID for chainID
    LET updateClientHeights == {dgr.height : dgr \in updateClientDgrs} IN    
    
    \* new chain record with client updated
    LET clientUpdatedChain == 
        IF clientNr \in DOMAIN chain.clientStates 
        THEN [chain EXCEPT !.clientStates = 
                [chain.clientStates EXCEPT ![clientNr] =
                    \* if clientNr is a valid client number
                    IF /\ clientNr \in DOMAIN chain.clientStates
                    \* if the slot at clientNr holds a client with clientID
                       /\ chain.clientStates[clientNr].clientID = clientID
                    THEN [chain.clientStates[clientNr] EXCEPT !.heights = 
                            chain.clientStates[clientNr].heights \union updateClientHeights]
                    ELSE chain.clientStates[clientNr]
             ]]
        ELSE chain IN
   
    clientUpdatedChain    

=============================================================================
\* Modification History
\* Last modified Wed Apr 14 18:46:39 CEST 2021 by ilinastoilkovska
\* Created Tue Apr 07 16:42:47 CEST 2020 by ilinastoilkovska
