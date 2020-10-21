-------------------------- MODULE ClientHandlers ---------------------------

(***************************************************************************
 This module contains definitions of operators that are used to handle
 client datagrams
 ***************************************************************************)

EXTENDS Integers, FiniteSets, RelayerDefinitions

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
    LET createClientHeights == AsSetInt({dgr.height : dgr \in createClientDgrs}) IN  
    
    \* new chain record with clients created
    LET clientCreateChain == [
            chain EXCEPT !.counterpartyClientHeights = 
                \* if the set of counterparty client heights is not empty or
                \* if the set of heights from datagrams is empty
                IF \/ chain.counterpartyClientHeights /= AsSetInt({}) 
                   \/ createClientHeights = AsSetInt({})
                \* then discard CreateClient datagrams  
                THEN AsSetInt(chain.counterpartyClientHeights)
                \* otherwise, create counterparty client with height Max(createClientHeights)  
                ELSE {Max(createClientHeights)}
         ] IN

    clientCreateChain

\* Handle "ClientUpdate" datagrams
HandleClientUpdate(chainID, chain, datagrams) ==     
    \* max client height of chain
    LET maxClientHeight == IF chain.counterpartyClientHeights /= AsSetInt({})
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
            chain EXCEPT !.counterpartyClientHeights = 
                \* if set of counterparty client heights is empty
                IF chain.counterpartyClientHeights = AsSetInt({})
                \* then discard ClientUpdate datagrams  
                THEN chain.counterpartyClientHeights
                \* otherwise, if set of heights from datagrams is not empty
                ELSE IF updateClientHeights /= AsSetInt({})
                     \* then update counterparty client heights with updateClientHeights
                     THEN chain.counterpartyClientHeights \union updateClientHeights
                     \* otherwise, do not update client heights
                     ELSE chain.counterpartyClientHeights
         ] IN
   
    clientUpdatedChain    

=============================================================================
\* Modification History
\* Last modified Thu Sep 10 15:43:27 CEST 2020 by ilinastoilkovska
\* Created Tue Apr 07 16:42:47 CEST 2020 by ilinastoilkovska
