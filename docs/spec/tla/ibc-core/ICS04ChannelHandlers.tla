------------------------ MODULE ICS04ChannelHandlers -----------------------

(***************************************************************************
 This module contains definitions of operators that are used to handle
 channel datagrams
 ***************************************************************************)

EXTENDS Integers, FiniteSets, IBCCoreDefinitions         

(***************************************************************************
 Channel datagram handlers
 ***************************************************************************)

\* Handle "ChanOpenInit" datagrams
HandleChanOpenInit(chainID, chain, datagrams) ==
    \* get chainID's connection end
    LET connectionEnd == chain.connectionEnd IN
    \* get "ChanOpenInit" datagrams, with a valid port and channel ID
    LET chanOpenInitDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ChanOpenInit"
                            /\ dgr.portID = GetPortID(chainID)
                            /\ dgr.channelID = GetChannelID(chainID)} IN
    
    \* if there are valid "ChanOpenInit" datagrams and the connection is not "UNINIT", 
    \* initialize the channel end and update the chain
    IF /\ chanOpenInitDgrs /= AsSetDatagrams({}) 
       /\ connectionEnd.state /= "UNINIT" 
       /\ connectionEnd.channelEnd.state = "UNINIT"
    THEN LET chanOpenInitDgr == CHOOSE dgr \in chanOpenInitDgrs : TRUE IN
         LET chanOpenInitChannelEnd == 
             IF connectionEnd.channelEnd.order = "ORDERED" 
             THEN AsChannelEnd([
                    state |-> "INIT",
                    order |-> "ORDERED",
                    nextSendSeq |-> 1,
                    nextRcvSeq |-> 1,
                    nextAckSeq |-> 1,
                    portID |-> chanOpenInitDgr.portID,
                    channelID |-> chanOpenInitDgr.channelID,
                    counterpartyPortID |-> chanOpenInitDgr.counterpartyPortID,
                    counterpartyChannelID |-> chanOpenInitDgr.counterpartyChannelID
                  ])
             ELSE AsChannelEnd([ 
                    state |-> "INIT",
                    order |-> "UNORDERED",
                    portID |-> chanOpenInitDgr.portID,
                    channelID |-> chanOpenInitDgr.channelID,
                    counterpartyPortID |-> chanOpenInitDgr.counterpartyPortID,
                    counterpartyChannelID |-> chanOpenInitDgr.counterpartyChannelID
                  ]) IN 
         LET chanOpenInitConnectionEnd == AsConnectionEnd([
             chain.connectionEnd EXCEPT !.channelEnd = chanOpenInitChannelEnd
         ]) IN
         LET chanOpenInitChain == AsChainStore([
             chain EXCEPT !.connectionEnd = chanOpenInitConnectionEnd            
         ]) IN
         
         chanOpenInitChain
    
    \* otherwise, do not update the chain store
    ELSE chain

\* Handle "ChanOpenTry" datagrams
HandleChanOpenTry(chainID, chain, datagrams) ==
    \* get chainID's connection end
    LET connectionEnd == chain.connectionEnd IN
    \* get "ChanOpenTry" datagrams, with a valid port and channel ID
    LET chanOpenTryDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ChanOpenTry"
                            /\ dgr.portID = GetPortID(chainID)
                            /\ dgr.channelID = GetChannelID(chainID)
                            /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    \* if there are valid "ChanOpenTry" datagrams and the connection is "OPEN", 
    \* update the channel end
    IF /\ chanOpenTryDgrs /= AsSetDatagrams({}) 
       /\ chain.connectionEnd = "OPEN" 
    THEN LET chanOpenTryDgr == CHOOSE dgr \in chanOpenTryDgrs : TRUE IN
         \* if the channel end is uninitialized
         IF \/ connectionEnd.channelEnd.state = "UNINIT"
         \* of if it is initialized, and all fields match the datagram fields
            \/ /\ connectionEnd.channelEnd.state = "INIT"
               /\ connectionEnd.channelEnd.counterpartyPortID 
                    = chanOpenTryDgr.counterpartyPortID
               /\ connectionEnd.channelEnd.counterpartyChannelID 
                    = chanOpenTryDgr.counterpartyChannelID
         \* update the channel end in the chain store           
         THEN LET chanOpenTryChannelEnd == 
                IF connectionEnd.channelEnd.order = "ORDERED" 
                THEN AsChannelEnd([
                        state |-> "TRYOPEN",
                        order |-> "ORDERED",
                        nextSendSeq |-> 1,
                        nextRcvSeq |-> 1,
                        nextAckSeq |-> 1,
                        portID |-> chanOpenTryDgr.portID,
                        channelID |-> chanOpenTryDgr.channelID,
                        counterpartyPortID |-> chanOpenTryDgr.counterpartyPortID,
                        counterpartyChannelID |-> chanOpenTryDgr.counterpartyChannelID
                  ])
                ELSE AsChannelEnd([
                        state |-> "TRYOPEN",
                        order |-> "UNORDERED",
                        portID |-> chanOpenTryDgr.portID,
                        channelID |-> chanOpenTryDgr.channelID,
                        counterpartyPortID |-> chanOpenTryDgr.counterpartyPortID,
                        counterpartyChannelID |-> chanOpenTryDgr.counterpartyChannelID
                  ]) IN 
       
              LET chanOpenTryConnectionEnd == AsConnectionEnd([
                  connectionEnd EXCEPT !.channelEnd = chanOpenTryChannelEnd
              ]) IN
              
              LET chanOpenTryChain == AsChainStore([
                  chain EXCEPT !.connectionEnd = chanOpenTryConnectionEnd
              ]) IN
                 
              chanOpenTryChain

    \* otherwise, do not update the chain store
         ELSE chain
    ELSE chain

\* Handle "ChanOpenAck" datagrams
HandleChanOpenAck(chainID, chain, datagrams) ==
    \* get chainID's connection end
    LET connectionEnd == chain.connectionEnd IN
    \* get chainID's channel end
    LET channelEnd == connectionEnd.channelEnd IN
    \* get "ChanOpenAck" datagrams, with a valid channel ID
    LET chanOpenAckDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ChanOpenAck"
                            /\ dgr.portID = channelEnd.portID
                            /\ dgr.channelID = channelEnd.channelID
                            /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    \* if there are valid "ChanOpenAck" datagrams, update the channel end
    IF /\ chanOpenAckDgrs /= AsSetDatagrams({}) 
       /\ connectionEnd.state = "OPEN"
    THEN \* if the channel end on the chain is in "INIT" or it is in "TRYOPEN",   
         \* update the channel end   
         IF \/ channelEnd.state = "INIT"
            \/ channelEnd.state = "TRYOPEN"
         THEN LET chanOpenAckDgr == CHOOSE dgr \in chanOpenAckDgrs : TRUE IN
              LET chanOpenAckChannelEnd == AsChannelEnd([
                  channelEnd EXCEPT !.state = "OPEN"
              ]) IN
              LET chanOpenAckConnectionEnd == AsConnectionEnd([ 
                  connectionEnd EXCEPT !.channelEnd = chanOpenAckChannelEnd
              ]) IN
              LET chanOpenAckChain == AsChainStore([
                  chain EXCEPT !.connectionEnd = chanOpenAckConnectionEnd
              ]) IN
              
              chanOpenAckChain

    \* otherwise, do not update the chain store
         ELSE chain
    ELSE chain
    

\* Handle "ChanOpenConfirm" datagrams
HandleChanOpenConfirm(chainID, chain, datagrams) ==
    \* get chainID's connection end
    LET connectionEnd == chain.connectionEnd IN
    \* get chainID's channel end
    LET channelEnd == connectionEnd.channelEnd IN
    \* get "ChanOpenConfirm" datagrams, with a valid channel ID 
    LET chanOpenConfirmDgrs == {dgr \in datagrams : 
                                /\ dgr.type = "ChanOpenConfirm"
                                /\ dgr.portID = channelEnd.portID
                                /\ dgr.channelID = channelEnd.channelID
                                /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    \* if there are valid "ChanOpenConfirm" datagrams, update the channel end
    IF /\ chanOpenConfirmDgrs /= AsSetDatagrams({}) 
       /\ connectionEnd.state = "OPEN"
    THEN \* if the channel end on the chain is in "TRYOPEN", update the channel end 
         IF channelEnd.state = "TRYOPEN"
         THEN LET chanOpenConfirmDgr == CHOOSE dgr \in chanOpenConfirmDgrs : TRUE IN
              LET chanOpenConfirmChannelEnd == AsChannelEnd([
                  channelEnd EXCEPT !.state = "OPEN"
              ]) IN
              LET chanOpenConfirmConnectionEnd == AsConnectionEnd([ 
                  connectionEnd EXCEPT !.channelEnd = chanOpenConfirmChannelEnd
              ]) IN
              LET chanOpenConfirmChain == AsChainStore([
                  chain EXCEPT !.connectionEnd = chanOpenConfirmConnectionEnd
              ]) IN
                 
              chanOpenConfirmChain

    \* otherwise, do not update the chain store
         ELSE chain
    ELSE chain
    
\* Handle "ChanCloseInit" datagrams
HandleChanCloseInit(chainID, chain, datagrams) ==
    \* get chainID's connection end
    LET connectionEnd == chain.connectionEnd IN
    \* get chainID's channel end
    LET channelEnd == connectionEnd.channelEnd IN
    \* get "ChanCloseInit" datagrams, with a valid channel ID 
    LET chanCloseInitDgrs == {dgr \in datagrams : 
                              /\ dgr.type = "ChanCloseInit"
                              /\ dgr.portID = channelEnd.portID
                              /\ dgr.channelID = channelEnd.channelID} IN
    
    \* if there are valid "ChanCloseInit" datagrams
    IF /\ chanCloseInitDgrs /= AsSetDatagrams({})
    \* and the channel end is neither UNINIT nor CLOSED
       /\ channelEnd.state \notin {"UNINIT", "CLOSED"}
    \* and the connection end is OPEN   
       /\ connectionEnd.state = "OPEN"
    THEN \* then close the channel end
         LET chanCloseInitChannelEnd == AsChannelEnd([
             channelEnd EXCEPT !.state = "CLOSED"
         ]) IN
         LET chanCloseInitConnectionEnd == AsConnectionEnd([ 
             connectionEnd EXCEPT !.channelEnd = chanCloseInitChannelEnd
         ]) IN
         LET chanCloseInitChain == AsChainStore([
             chain EXCEPT !.connectionEnd = chanCloseInitConnectionEnd
         ]) IN
         
         chanCloseInitChain
    
    \* otherwise, do not update the chain store
    ELSE chain

\* Handle "ChanCloseConfirm" datagrams
HandleChanCloseConfirm(chainID, chain, datagrams) ==
    \* get chainID's connection end
    LET connectionEnd == chain.connectionEnd IN
    \* get chainID's channel end
    LET channelEnd == connectionEnd.channelEnd IN
    \* get "ChanCloseConfirm" datagrams, with a valid channel ID 
    LET chanCloseConfirmDgrs == {dgr \in datagrams : 
                                 /\ dgr.type = "ChanCloseConfirm"
                                 /\ dgr.portID = channelEnd.portID
                                 /\ dgr.channelID = channelEnd.channelID
                                 /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    \* if there are valid "ChanCloseConfirm" datagrams
    IF /\ chanCloseConfirmDgrs /= AsSetDatagrams({})
    \* and the channel end is neither UNINIT nor CLOSED
       /\ channelEnd.state \notin {"UNINIT", "CLOSED"}
    \* and the connection end is OPEN   
       /\ connectionEnd.state = "OPEN"
    THEN \* then close the channel end
         LET chanCloseConfirmChannelEnd == AsChannelEnd([
             channelEnd EXCEPT !.state = "CLOSED"
         ]) IN
         LET chanCloseConfirmConnectionEnd == AsConnectionEnd([ 
             connectionEnd EXCEPT !.channelEnd = chanCloseConfirmChannelEnd
         ]) IN
         LET chanCloseConfirmChain == AsChainStore([
             chain EXCEPT !.connectionEnd = chanCloseConfirmConnectionEnd
         ]) IN
         
         chanCloseConfirmChain
    
    \* otherwise, do not update the chain store
    ELSE chain

=============================================================================
\* Modification History
\* Last modified Mon Nov 30 13:59:29 CET 2020 by ilinastoilkovska
\* Created Tue Apr 07 16:58:02 CEST 2020 by ilinastoilkovska
