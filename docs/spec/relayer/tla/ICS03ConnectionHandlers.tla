---------------------- MODULE ICS03ConnectionHandlers ----------------------

(***************************************************************************
 This module contains definitions of operators that are used to handle
 connection datagrams
 ***************************************************************************)

EXTENDS Integers, FiniteSets, IBCCoreDefinitions     

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
             counterpartyConnectionID |-> connOpenInitDgr.counterpartyConnectionID,
             clientID |-> connOpenInitDgr.clientID,
             counterpartyClientID |-> connOpenInitDgr.counterpartyClientID,
             versions |-> chain.connectionEnd.versions,
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
                            /\ dgr.desiredConnectionID = GetConnectionID(chainID)
                            /\ dgr.consensusHeight <= chain.height
                            /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN

    IF connOpenTryDgrs /= AsSetDatagrams({})
    \* if there are valid "ConnOpenTry" datagrams, update the connection end 
    THEN LET connOpenTryDgr == CHOOSE dgr \in connOpenTryDgrs : TRUE IN
         LET versionIntersection == chain.connectionEnd.versions \intersect connOpenTryDgr.versions IN
       
         \* if the versions from the datagram overlap with the supported versions of the connnection end
         IF /\ versionIntersection /= AsSetInt({})
         \* if the connection end is uninitialized
            /\ \/ chain.connectionEnd.state = "UNINIT"
         \* of if it is initialized, and all fields match the datagram fields
               \/ /\ chain.connectionEnd.state = "INIT"
                  /\ chain.connectionEnd.connectionID  
                      = connOpenTryDgr.desiredConnectionID
                  /\ chain.connectionEnd.counterpartyConnectionID 
                      = connOpenTryDgr.counterpartyConnectionID
                  /\ chain.connectionEnd.clientID 
                      = connOpenTryDgr.clientID
                  /\ chain.connectionEnd.counterpartyClientID 
                      = connOpenTryDgr.counterpartyClientID
         \* update the connection end in the chain store
         THEN LET connOpenTryConnectionEnd == AsConnectionEnd([
                state |-> "TRYOPEN",
                connectionID |-> connOpenTryDgr.desiredConnectionID,
                counterpartyConnectionID |-> connOpenTryDgr.counterpartyConnectionID,
                clientID |-> connOpenTryDgr.clientID,
                counterpartyClientID |-> connOpenTryDgr.counterpartyClientID,
                versions |-> PickVersion(versionIntersection),
                channelEnd |-> chain.connectionEnd.channelEnd 
          ]) IN 
              LET connOpenTryChain == AsChainStore([
                  chain EXCEPT !.connectionEnd = connOpenTryConnectionEnd
              ]) IN
                
              connOpenTryChain

    \* otherwise, do not update the chain store
         ELSE chain
    ELSE chain

\* Handle "ConnOpenAck" datagrams
HandleConnOpenAck(chainID, chain, datagrams) ==
    \* get existing connection end
    LET connectionEnd == chain.connectionEnd IN
    \* get "ConnOpenAck" datagrams, with a valid connection ID and valid height
    LET connOpenAckDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ConnOpenAck"
                            /\ dgr.connectionID = connectionEnd.connectionID
                            /\ dgr.consensusHeight <= chain.height
                            /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    \* if there are valid "ConnOpenAck" datagrams, update the connection end 
    IF connOpenAckDgrs /= AsSetDatagrams({})
    THEN LET connOpenAckDgr == CHOOSE dgr \in connOpenAckDgrs : TRUE IN
         \* if the connection end on the chain is in "INIT" and the version set 
         \* from the datagram is a subset of the supported versions in the connection end 
         IF \/ /\ connectionEnd.state = "INIT"
               /\ connOpenAckDgr.versions \subseteq connectionEnd.versions
         \* or the connection end is in "TRYOPEN" and the version set
         \* from the datagram is equal to the version set in the connection end 
            \/ /\ connectionEnd.state = "TRYOPEN"
               /\ connOpenAckDgr.versions = connectionEnd.versions
         \* update the connection end       
         THEN LET connOpenAckConnectionEnd == AsConnectionEnd([ 
                    connectionEnd EXCEPT !.state = "OPEN", 
                                         !.versions = connOpenAckDgr.versions
              ]) IN
              LET connOpenAckChain == AsChainStore([
                  chain EXCEPT !.connectionEnd = connOpenAckConnectionEnd
              ]) IN
              
              connOpenAckChain

    \* otherwise, do not update the chain store
         ELSE chain
    ELSE chain

    

\* Handle "ConnOpenConfirm" datagrams
HandleConnOpenConfirm(chainID, chain, datagrams) ==
    \* get existing connection end
    LET connectionEnd == chain.connectionEnd IN
    \* get "ConnOpenConfirm" datagrams, with a valid connection ID and valid height
    LET connOpenConfirmDgrs == {dgr \in datagrams : 
                                /\ dgr.type = "ConnOpenConfirm"
                                /\ dgr.connectionID = connectionEnd.connectionID
                                /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    IF connOpenConfirmDgrs /= AsSetDatagrams({})
    \* if there are valid "connOpenConfirmDgrs" datagrams, update the connection end 
    THEN IF connectionEnd.state = "TRYOPEN"
         \* if the connection end on the chain is in "TRYOPEN", update the connection end       
         THEN LET connOpenConfirmDgr == CHOOSE dgr \in connOpenConfirmDgrs : TRUE IN
              LET connOpenConfirmConnectionEnd == AsConnectionEnd([ 
                  connectionEnd EXCEPT !.state = "OPEN"
              ]) IN
              LET connOpenConfirmChain == AsChainStore([
                  chain EXCEPT !.connectionEnd = connOpenConfirmConnectionEnd
              ]) IN
              
              connOpenConfirmChain

    \* otherwise, do not update the chain store
         ELSE chain
    ELSE chain

=============================================================================
\* Modification History
\* Last modified Mon Nov 30 13:56:55 CET 2020 by ilinastoilkovska
\* Created Tue Apr 07 16:09:26 CEST 2020 by ilinastoilkovska
