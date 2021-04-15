----------------------- MODULE ICS02ClientHandlers -------------------------

(***************************************************************************
 This module contains definitions of operators that are used to handle
 client create and update datagrams.
 ***************************************************************************)

EXTENDS Integers, FiniteSets, IBCCoreDefinitions

(***************************************************************************
 Client datagram handlers
 ***************************************************************************)
   
\* Handle "CreateClient" datagrams
\* @type: (Str, CHAINSTORE, Set(DATAGRAM)) => CHAINSTORE;
HandleCreateClient(chainID, chain, datagrams) == 
    \* get "CreateClient" datagrams with valid clientID
    LET createClientDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ClientCreate"
                            /\ dgr.clientID = GetCounterpartyClientID(chainID)} IN
    \* get heights in datagrams with correct counterparty clientID for chainID
    LET createClientHeights == {dgr.height : dgr \in createClientDgrs} IN  
    
    \* new chain record with clients created
    LET clientCreateChain == [
            chain EXCEPT !.counterpartyClientHeights = 
                \* if the set of counterparty client heights is not empty or
                \* if the set of heights from datagrams is empty
                IF \/ chain.counterpartyClientHeights /= {}
                   \/ createClientHeights = {}
                \* then discard CreateClient datagrams  
                THEN chain.counterpartyClientHeights
                \* otherwise, create counterparty client with height Max(createClientHeights)  
                ELSE {Max(createClientHeights)}
         ] IN

    clientCreateChain

\* Handle "ClientUpdate" datagrams
\* @type: (Str, CHAINSTORE, Set(DATAGRAM)) => CHAINSTORE;
HandleClientUpdate(chainID, chain, datagrams) ==     
    \* max client height for counterparty chain
    LET maxClientHeight == GetMaxCounterpartyClientHeight(chain) IN 
    \* get "ClientUpdate" datagrams with valid clientID
    LET updateClientDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ClientUpdate"
                            /\ dgr.clientID = GetCounterpartyClientID(chainID)
    \* Note: the check maxClientHeight < dgr.height can be commented out in case 
    \* older headers can be installed for the client
                            /\ maxClientHeight < dgr.height
                            } IN
    \* get heights in datagrams with correct counterparty clientID for chainID
    LET updateClientHeights == {dgr.height : dgr \in updateClientDgrs} IN    

    \* new chain record with clients updated
    LET clientUpdatedChain == [
            chain EXCEPT !.counterpartyClientHeights = 
                \* if set of counterparty client heights is empty
                IF chain.counterpartyClientHeights = {}
                \* then discard ClientUpdate datagrams  
                THEN chain.counterpartyClientHeights
                \* otherwise, if set of heights from datagrams is not empty
                ELSE IF updateClientHeights /= {}
                     \* then update counterparty client heights with updateClientHeights
                     THEN chain.counterpartyClientHeights \union updateClientHeights
                     \* otherwise, do not update client heights
                     ELSE chain.counterpartyClientHeights
         ] IN
   
    clientUpdatedChain    

=============================================================================
\* Modification History
\* Last modified Mon Apr 12 14:23:14 CEST 2021 by ilinastoilkovska
\* Created Tue Apr 07 16:42:47 CEST 2020 by ilinastoilkovska
