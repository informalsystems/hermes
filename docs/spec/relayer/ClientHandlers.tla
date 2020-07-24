-------------------------- MODULE ClientHandlers ---------------------------

(***************************************************************************
 This module contains definitions of operators that are used to handle
 client datagrams
 ***************************************************************************)

EXTENDS Naturals, FiniteSets, RelayerDefinitions

(***************************************************************************
 Client datagram handlers
 ***************************************************************************)
    
\* client heights: 
\* good version: add all client heights from datagrams to counterpartyClientHeights
\* bad version: add only Max of client heights from datagrams to counterpartyClientHeights
\*              if Max > Max(counterpartyClientHeights)
    
\* Handle "CreateClient" datagrams
HandleCreateClient(chainID, chain, datagrams) == 
    \* get "CreateClient" datagrams with valid clientID
    LET createClientDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "CreateClient"
                            /\ dgr.clientID = GetCounterpartyClientID(chainID)} IN
    \* get heights in datagrams with correct counterparty clientID for chainID
    LET createClientHeights == {dgr.height : dgr \in createClientDgrs} IN  
    
    \* new chain record with clients created
    LET clientCreateChain == [
            height |-> chain.height,
            counterpartyClientHeights |-> 
                \* if the set of counterparty client heights is not empty and
                \* if the set of heights from datagrams is empty
                IF chain.counterpartyClientHeights /= {} \/ createClientHeights = {}
                \* then discard CreateClient datagrams  
                THEN chain.counterpartyClientHeights
                \* otherwise, create counterparty client with height Max(createClientHeights)  
                ELSE {Max(createClientHeights)},
            connectionEnd |-> chain.connectionEnd
         ] IN

   clientCreateChain
 
\* Handle "ClientUpdate" datagrams
HandleUpdateClient(chainID, chain, datagrams) ==     
    \* max client height of chain
    LET maxClientHeight == IF chain.counterpartyClientHeights /= {}
                           THEN Max(chain.counterpartyClientHeights)
                           ELSE 0 IN 
    \* get "ClientUpdate" datagrams with valid clientID
    LET updateClientDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ClientUpdate"
                            /\ dgr.clientID = GetCounterpartyClientID(chainID)
                            /\ maxClientHeight < dgr.height} IN
    \* get heights in datagrams with correct counterparty clientID for chainID
    LET updateClientHeights == {dgr.height : dgr \in updateClientDgrs} IN    

    \* new chain record with clients updated
    LET clientUpdatedChain == [
            height |-> chain.height,
            counterpartyClientHeights |-> 
                \* if set of counterparty client heights is empty
                IF chain.counterpartyClientHeights = {}
                \* then discard ClientUpdate datagrams  
                THEN chain.counterpartyClientHeights
                \* otherwise, if set of heights from datagrams is not empty
                ELSE IF updateClientHeights /= {}
                     \* then update counterparty client heights with updateClientHeights
                     THEN chain.counterpartyClientHeights \union updateClientHeights
                     \* otherwise, do not update client heights
                     ELSE chain.counterpartyClientHeights,
            connectionEnd |-> chain.connectionEnd
         ] IN
   
    clientUpdatedChain
        

=============================================================================
\* Modification History
\* Last modified Thu Jul 09 13:12:01 CEST 2020 by ilinastoilkovska
\* Created Tue Apr 07 16:42:47 CEST 2020 by ilinastoilkovska
