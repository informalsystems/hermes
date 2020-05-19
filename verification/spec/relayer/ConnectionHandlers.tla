------------------------- MODULE ConnectionHandlers -------------------------

(***************************************************************************
 This module contains definitions of operators that are used to handle
 connection datagrams
 ***************************************************************************)

EXTENDS Naturals, FiniteSets

ConnectionIDs == {"connAtoB", "connBtoA"}
nullConnectionID == "none"

ConnectionStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN"}

(***************************************************************************
 Connection helper operators
 ***************************************************************************)

\* get the connection ID of the connection end at chainID
GetConnectionID(chainID) ==
    IF chainID = "chainA"
    THEN "connAtoB"
    ELSE IF chainID = "chainB"
         THEN "connBtoA"
         ELSE nullConnectionID      

\* get the connection ID of the connection end at chainID's counterparty chain
GetCounterpartyConnectionID(chainID) ==
    IF chainID = "chainA"
    THEN "connBtoA"
    ELSE IF chainID = "chainB"
         THEN "connAtoB"
         ELSE nullConnectionID      

(***************************************************************************
 Connection datagram handlers
 ***************************************************************************)
 
\* Handle "ConnOpenInit" datagrams
HandleConnOpenInit(chainID, chain, datagrams) ==
    \* get "ConnOpenInit" datagrams, with a valid connection ID
    LET connOpenInitDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ConnOpenInit"
                            /\ dgr.connectionID = GetConnectionID(chainID)} IN
    
    IF connOpenInitDgrs /= {} 
    \* if there are valid "ConnOpenInit" datagrams, create a new connection end and update the chain
    \* TODO: check here if connection is already in INIT?
    THEN LET connOpenInitDgr == CHOOSE dgr \in connOpenInitDgrs : TRUE IN
         LET connOpenInitConnectionEnd == [
             state |-> "INIT",
             connectionID |-> connOpenInitDgr.connectionID,
             clientID |-> connOpenInitDgr.clientID,
             counterpartyConnectionID |-> connOpenInitDgr.counterpartyConnectionID,
             counterpartyClientID |-> connOpenInitDgr.counterpartyClientID,
             channelEnd |-> chain.connectionEnd.channelEnd 
         ] IN 
         LET connOpenInitChain == [
             chain EXCEPT !.connectionEnd = connOpenInitConnectionEnd
         ] IN
        
         connOpenInitChain
    \* otherwise, do not update the chain     
    ELSE chain
    

\* Handle "ConnOpenTry" datagrams
HandleConnOpenTry(chainID, chain, datagrams) ==
    \* get "ConnOpenTry" datagrams, with a valid connection ID and valid height
    LET connOpenTryDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ConnOpenTry"
                            /\ dgr.desiredConnectionID = GetConnectionID(chainID)
                            /\ dgr.consensusHeight <= chain.height
                            /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
                            \* TODO: check dgr.proofHeight \in chain.counterpartyClientHeight
    
    IF connOpenTryDgrs /= {}
    \* if there are valid "ConnOpenTry" datagrams, update the connection end 
    THEN LET connOpenTryDgr == CHOOSE dgr \in connOpenTryDgrs : TRUE IN
         LET connOpenTryConnectionEnd == [
                state |-> "TRYOPEN",
                connectionID |-> connOpenTryDgr.desiredConnectionID,
                clientID |-> connOpenTryDgr.clientID,
                counterpartyConnectionID |-> connOpenTryDgr.counterpartyConnectionID,
                counterpartyClientID |-> connOpenTryDgr.counterpartyClientID,
                channelEnd |-> chain.connectionEnd.channelEnd 
            ] IN 
       
         IF \/ chain.connectionEnd.state = "UNINIT"
            \/ /\ chain.connectionEnd.state = "INIT"
               /\ chain.connectionEnd.counterpartyConnectionID 
                    = connOpenTryConnectionEnd.counterpartyConnectionID
               /\ chain.connectionEnd.clientID 
                    = connOpenTryConnectionEnd.clientID
               /\ chain.connectionEnd.counterpartyClientID 
                    = connOpenTryConnectionEnd.counterpartyClientID 
         \* if the connection end on the chain is in "UNINIT" or it is in "INIT",  
         \* but the fields are the same as in the datagram, update the connection end     
         THEN LET connOpenTryChain == [
                  chain EXCEPT !.connectionEnd = connOpenTryConnectionEnd
                ] IN
                
              connOpenTryChain
         \* otherwise, do not update the chain
         ELSE chain
    \* otherwise, do not update the chain     
    ELSE chain


\* Handle "ConnOpenAck" datagrams
HandleConnOpenAck(chainID, chain, datagrams) ==
    \* get "ConnOpenAck" datagrams, with a valid connection ID and valid height
    LET connOpenAckDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ConnOpenAck"
                            /\ dgr.connectionID = GetConnectionID(chainID)
                            /\ dgr.consensusHeight <= chain.height
                            /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    IF connOpenAckDgrs /= {}
    \* if there are valid "ConnOpenAck" datagrams, update the connection end 
    THEN IF \/ chain.connectionEnd.state = "INIT"
            \/ chain.connectionEnd.state = "TRYOPEN"
         \* if the connection end on the chain is in "INIT" or it is in "TRYOPEN",   
         \* update the connection end       
         THEN LET connOpenAckDgr == CHOOSE dgr \in connOpenAckDgrs : TRUE IN
              LET connOpenAckConnectionEnd == [ 
                  chain.connectionEnd EXCEPT !.state = "OPEN", 
                                             !.connectionID = connOpenAckDgr.connectionID
                ] IN
              LET connOpenAckChain == [
                  chain EXCEPT !.connectionEnd = connOpenAckConnectionEnd
                ] IN
              
              connOpenAckChain                
         \* otherwise, do not update the chain
         ELSE chain
    \* otherwise, do not update the chain     
    ELSE chain


\* Handle "ConnOpenConfirm" datagrams
HandleConnOpenConfirm(chainID, chain, datagrams) ==
    \* get "ConnOpenConfirm" datagrams, with a valid connection ID and valid height
    LET connOpenConfirmDgrs == {dgr \in datagrams : 
                                /\ dgr.type = "ConnOpenConfirm"
                                /\ dgr.connectionID = GetConnectionID(chainID)
                                /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    IF connOpenConfirmDgrs /= {}
    \* if there are valid "connOpenConfirmDgrs" datagrams, update the connection end 
    THEN IF chain.connectionEnd.state = "TRYOPEN"
         \* if the connection end on the chain is in "TRYOPEN", update the connection end       
         THEN LET connOpenConfirmDgr == CHOOSE dgr \in connOpenConfirmDgrs : TRUE IN
              LET connOpenConfirmConnectionEnd == [ 
                  chain.connectionEnd EXCEPT !.state = "OPEN",
                                             !.connectionID = connOpenConfirmDgr.connectionID
                ] IN
              LET connOpenConfirmChain == [
                  chain EXCEPT !.connectionEnd = connOpenConfirmConnectionEnd
                ] IN
              
              connOpenConfirmChain                
         \* otherwise, do not update the chain
         ELSE chain
    \* otherwise, do not update the chain     
    ELSE chain

=============================================================================
\* Modification History
\* Last modified Thu May 14 16:29:33 CEST 2020 by ilinastoilkovska
\* Created Tue Apr 07 16:09:26 CEST 2020 by ilinastoilkovska
