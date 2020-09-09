------------------------- MODULE ConnectionHandlers -------------------------

(***************************************************************************
 This module contains definitions of operators that are used to handle
 connection datagrams
 ***************************************************************************)

EXTENDS Integers, FiniteSets, RelayerDefinitions     

(***************************************************************************
 Connection datagram handlers
 ***************************************************************************)
 
\* Handle "ConnOpenInit" datagrams
HandleConnOpenInit(chainID, chain, datagrams) ==
    \* get "ConnOpenInit" datagrams, with a valid connection ID
    LET connOpenInitDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ConnOpenInit"
                            /\ dgr.connectionID = GetConnectionID(chainID)} IN
    
    \* if there are valid "ConnOpenInit" datagrams, create a new connection end 
    \* and update the chain store
    IF /\ connOpenInitDgrs /= AsSetDatagrams({}) 
       /\ chain.connectionEnd.state = "UNINIT"
    THEN LET connOpenInitDgr == CHOOSE dgr \in connOpenInitDgrs : TRUE IN
         LET connOpenInitConnectionEnd == AsConnectionEnd([
             state |-> "INIT",
             connectionID |-> connOpenInitDgr.connectionID,
             clientID |-> connOpenInitDgr.clientID,
             counterpartyConnectionID |-> connOpenInitDgr.counterpartyConnectionID,
             counterpartyClientID |-> connOpenInitDgr.counterpartyClientID,
             channelEnd |-> chain.connectionEnd.channelEnd 
         ]) IN 
         LET connOpenInitChain == AsChainStore([
             chain EXCEPT !.connectionEnd = connOpenInitConnectionEnd
         ]) IN
         
         connOpenInitChain

    \* otherwise, do not update the chain store
    ELSE chain


\* Handle "ConnOpenTry" datagrams
HandleConnOpenTry(chainID, chain, datagrams) ==
    \* get "ConnOpenTry" datagrams, with a valid connection ID and valid height
    LET connOpenTryDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ConnOpenTry"
                            /\ dgr.connectionID = GetConnectionID(chainID)
                            /\ dgr.consensusHeight <= chain.height
                            /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN

    IF connOpenTryDgrs /= AsSetDatagrams({})
    \* if there are valid "ConnOpenTry" datagrams, update the connection end 
    THEN LET connOpenTryDgr == CHOOSE dgr \in connOpenTryDgrs : TRUE IN
         LET connOpenTryConnectionEnd == AsConnectionEnd([
                state |-> "TRYOPEN",
                connectionID |-> connOpenTryDgr.connectionID,
                clientID |-> connOpenTryDgr.clientID,
                counterpartyConnectionID |-> connOpenTryDgr.counterpartyConnectionID,
                counterpartyClientID |-> connOpenTryDgr.counterpartyClientID,
                channelEnd |-> chain.connectionEnd.channelEnd 
          ]) IN 
       
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
         THEN LET connOpenTryChain == AsChainStore([
                  chain EXCEPT !.connectionEnd = connOpenTryConnectionEnd
              ]) IN
                
              connOpenTryChain
         \* otherwise, do not update the chain store
         ELSE chain
    \* otherwise, do not update the chain store
    ELSE chain

\* Handle "ConnOpenAck" datagrams
HandleConnOpenAck(chainID, chain, datagrams) ==
    \* get "ConnOpenAck" datagrams, with a valid connection ID and valid height
    LET connOpenAckDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ConnOpenAck"
                            /\ dgr.connectionID = GetConnectionID(chainID)
                            /\ dgr.consensusHeight <= chain.height
                            /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    IF connOpenAckDgrs /= AsSetDatagrams({})
    \* if there are valid "ConnOpenAck" datagrams, update the connection end 
    THEN IF \/ chain.connectionEnd.state = "INIT"
            \/ chain.connectionEnd.state = "TRYOPEN"
         \* if the connection end on the chain is in "INIT" or it is in "TRYOPEN",   
         \* update the connection end       
         THEN LET connOpenAckDgr == CHOOSE dgr \in connOpenAckDgrs : TRUE IN
              LET connOpenAckConnectionEnd == AsConnectionEnd([ 
                  chain.connectionEnd EXCEPT !.state = "OPEN", 
                                             !.connectionID = connOpenAckDgr.connectionID
              ]) IN
              LET connOpenAckChain == AsChainStore([
                  chain EXCEPT !.connectionEnd = connOpenAckConnectionEnd
              ]) IN
              
              connOpenAckChain
         \* otherwise, do not update the chain store
         ELSE chain
    \* otherwise, do not update the chain store
    ELSE chain

    

\* Handle "ConnOpenConfirm" datagrams
HandleConnOpenConfirm(chainID, chain, datagrams) ==
    \* get "ConnOpenConfirm" datagrams, with a valid connection ID and valid height
    LET connOpenConfirmDgrs == {dgr \in datagrams : 
                                /\ dgr.type = "ConnOpenConfirm"
                                /\ dgr.connectionID = GetConnectionID(chainID)
                                /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    IF connOpenConfirmDgrs /= AsSetDatagrams({})
    \* if there are valid "connOpenConfirmDgrs" datagrams, update the connection end 
    THEN IF chain.connectionEnd.state = "TRYOPEN"
         \* if the connection end on the chain is in "TRYOPEN", update the connection end       
         THEN LET connOpenConfirmDgr == CHOOSE dgr \in connOpenConfirmDgrs : TRUE IN
              LET connOpenConfirmConnectionEnd == AsConnectionEnd([ 
                  chain.connectionEnd EXCEPT !.state = "OPEN",
                                             !.connectionID = connOpenConfirmDgr.connectionID
              ]) IN
              LET connOpenConfirmChain == AsChainStore([
                  chain EXCEPT !.connectionEnd = connOpenConfirmConnectionEnd
              ]) IN
              
              connOpenConfirmChain
         \* otherwise, do not update the chain store
         ELSE chain
    \* otherwise, do not update the chain store
    ELSE chain

=============================================================================
\* Modification History
\* Last modified Wed Sep 09 14:21:25 CEST 2020 by ilinastoilkovska
\* Created Tue Apr 07 16:09:26 CEST 2020 by ilinastoilkovska
