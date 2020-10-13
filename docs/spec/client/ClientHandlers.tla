-------------------------- MODULE ClientHandlers ---------------------------

(***************************************************************************
 This module contains definitions of operators that are used to handle
 client datagrams
 ***************************************************************************)

EXTENDS Integers, FiniteSets, ICS02Definitions

(***************************************************************************
 Client datagram handlers
 ***************************************************************************)
    
\* Handle "CreateClient" datagrams
HandleCreateClient(chainID, chain, clientID, datagrams) == 
    \* get "CreateClient" datagrams with valid clientID
    LET createClientDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "CreateClient"
                            /\ dgr.clientID = clientID} IN
    \* get heights in datagrams with correct counterparty clientID for chainID
    LET createClientHeights == AsSetInt({dgr.height : dgr \in createClientDgrs}) IN  
    
    \* new chain record with clients created
    LET clientCreateChain == [
            chain EXCEPT 
                !.client1 =
                \* if both clients are null 
                IF /\ chain.client1.clientID = nullClientID
                   /\ chain.client2.clientID = nullClientID
                \* if the set of heights from datagrams is not empty
                   /\ createClientHeights /= AsSetInt({}) 
                \* then create a client with clientID as client1
                THEN AsClient([clientID |-> AsID(clientID), heights |-> AsSetInt({Max(createClientHeights)})])
                \* otherwise, discard CreateClient datagrams  
                ELSE chain.client1,
                
                !.client2 =
                \* if client1 is created but client2 is not 
                IF /\ chain.client1.clientID /= nullClientID
                   /\ chain.client2.clientID = nullClientID
                \* if clientID is not the ID of client1 
                   /\ chain.client1.clientID /= clientID
                \* if the set of heights from datagrams is not empty
                   /\ createClientHeights /= AsSetInt({}) 
                \* then create a client with clientID as client2
                THEN AsClient([clientID |-> AsID(clientID), heights |-> AsSetInt({Max(createClientHeights)})])
                \* otherwise, discard CreateClient datagrams  
                ELSE chain.client2        
         ] IN

    clientCreateChain

\* Handle "ClientUpdate" datagrams
HandleClientUpdate(chainID, chain, clientID, datagrams) ==     
    \* max client height of chain
    LET maxClientHeight(clID) == 
        IF chain.client1.clientID = clID /\ chain.client1.heights /= AsSetInt({})
        THEN Max(chain.client1.heights)
        ELSE IF chain.client2.clientID = clID /\ chain.client2.heights /= AsSetInt({})
             THEN Max(chain.client2.heights)
             ELSE 0 IN 
    \* get "ClientUpdate" datagrams with valid clientID
    LET updateClientDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ClientUpdate"
                            /\ dgr.clientID = clientID
                            /\ maxClientHeight(clientID) < dgr.height} IN
    \* get heights in datagrams with correct counterparty clientID for chainID
    LET updateClientHeights == {dgr.height : dgr \in updateClientDgrs} IN    

    \* new chain record with clients updated
    LET clientUpdatedChain == [
            chain EXCEPT
                 !.client1 = 
                    \* if client1 is created 
                    IF /\ chain.client1.clientID /= nullClientID
                    \* if clientID is the ID of client1    
                       /\ chain.client1.clientID = clientID
                    \* then update the client
                    THEN [chain.client1 EXCEPT 
                                !.heights = chain.client1.heights \union updateClientHeights]
                    \* otherwise, discard ClientUpdate datagrams  
                    ELSE chain.client1,
                 !.client2 = 
                    \* if client2 is created 
                    IF /\ chain.client2.clientID /= nullClientID
                    \* if clientID is the ID of client1    
                       /\ chain.client2.clientID = clientID
                    \* then update the client
                    THEN [chain.client2 EXCEPT 
                                !.heights = chain.client2.heights \union updateClientHeights]
                    \* otherwise, discard ClientUpdate datagrams  
                    ELSE chain.client2        
         ] IN
   
    clientUpdatedChain    

=============================================================================
\* Modification History
\* Last modified Tue Oct 13 12:57:21 CEST 2020 by ilinastoilkovska
\* Created Tue Apr 07 16:42:47 CEST 2020 by ilinastoilkovska
