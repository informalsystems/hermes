-------------------------- MODULE ClientHandlers ---------------------------

(***************************************************************************
 This module contains definitions of operators that are used to handle
 client datagrams
 ***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS MaxHeight \* maximal height of all the chains in the system

ClientIDs == {"clA", "clB"}
nullClientID == "none"
nullHeight == 0

Heights == 1..MaxHeight 

Max(S) == CHOOSE x \in S: \A y \in S: y <= x

(***************************************************************************
 Client helper operators
 ***************************************************************************)

\* get the ID of chainID's counterparty chain    
GetCounterpartyChainID(chainID) ==
    IF chainID = "chainA" THEN "chainB" ELSE "chainA"    
 
\* get the client ID of the client for chainID 
GetClientID(chainID) ==
    IF chainID = "chainA" THEN "clA" ELSE "clB"
        
\* get the client ID of the client for chainID's counterparty chain           
GetCounterpartyClientID(chainID) ==
    IF chainID = "chainA" THEN "clB" ELSE "clA" 
    

(***************************************************************************
 Client datagram handlers
 ***************************************************************************)
    
\* Handle "CreateClient" datagrams
HandleCreateClient(chainID, chain, datagrams) == 
    \* get "CreateClient" datagrams with valid clientID
    LET createClientDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "CreateClient"
                            /\ dgr.clientID = GetCounterpartyClientID(chainID)} IN
    \* get heights in datagrams with correct counterparty clientID for chainID
    LET createClientHeights == {h \in Heights : \E dgr \in createClientDgrs : dgr.height = h} IN  
    
    \* new chain record with clients created
    LET clientCreateChain == [
            height |-> chain.height,
            counterpartyClientHeight |-> IF createClientHeights /= {}
                                         THEN Max(createClientHeights)
                                         ELSE chain.counterpartyClientHeight,
            connectionEnd |-> chain.connectionEnd
         ] IN

    IF chain.counterpartyClientHeight = nullHeight
    \* if the counterparty client height is null, create the client   
    THEN clientCreateChain
    \* otherwise, do not update the chain  
    ELSE chain 

\* Handle "ClientUpdate" datagrams
HandleUpdateClient(chainID, chain, datagrams) ==      
    \* get "ClientUpdate" datagrams with valid clientID
    LET updateClientDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ClientUpdate"
                            /\ dgr.clientID = GetCounterpartyClientID(chainID)} IN
    \* get heights in datagrams with correct counterparty clientID for chainID
    LET updateClientHeights == {h \in Heights : \E dgr \in updateClientDgrs : dgr.height = h} IN    

    \* new chain record with clients updated
    LET clientUpdatedChain == [
            height |-> chain.height,
            counterpartyClientHeight |-> IF updateClientHeights /= {}
                                         THEN Max(updateClientHeights)
                                         ELSE chain.counterpartyClientHeight,
            connectionEnd |-> chain.connectionEnd
         ] IN
    
\*    IF chain.counterpartyClientHeight < clientUpdatedChain.counterpartyClientHeight
    \* if the current height of the counterparty client is smaller than the new height, update it
\*    THEN clientUpdatedChain 
    \* otherwise, do not update the chain
\*    ELSE chain 
    clientUpdatedChain
        

=============================================================================
\* Modification History
\* Last modified Wed Apr 15 16:17:39 CEST 2020 by ilinastoilkovska
\* Created Tue Apr 07 16:42:47 CEST 2020 by ilinastoilkovska
