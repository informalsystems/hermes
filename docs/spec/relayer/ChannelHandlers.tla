-------------------------- MODULE ChannelHandlers --------------------------

(***************************************************************************
 This module contains definitions of operators that are used to handle
 channel datagrams
 ***************************************************************************)

EXTENDS Naturals, FiniteSets, RelayerDefinitions         

(***************************************************************************
 Channel datagram handlers
 ***************************************************************************)

\* Handle "ChanOpenInit" datagrams
HandleChanOpenInit(chainID, chain, datagrams) ==
    \* get chainID's channel end
    LET channelEnd == chain.connectionEnd.channelEnd IN
    \* get "ChanOpenInit" datagrams, with a valid channel ID
    LET chanOpenInitDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ChanOpenInit"
                            /\ dgr.channelID = GetChannelID(chainID)} IN
    
    \* if there are valid "ChanOpenInit" datagrams and the connection is not "UNINIT", 
    \* initialize the channel end and update the chain
    IF /\ chanOpenInitDgrs /= AsSetDatagrams({}) 
       /\ chain.connectionEnd.state /= "UNINIT" 
       /\ channelEnd.state = "UNINIT"
    THEN LET chanOpenInitDgr == CHOOSE dgr \in chanOpenInitDgrs : TRUE IN
         LET chanOpenInitChannelEnd == 
             IF channelEnd.order = "ORDERED" 
             THEN AsChannelEnd([channelEnd EXCEPT 
                    !.state = "INIT",
                    !.channelID = chanOpenInitDgr.channelID,
                    !.counterpartyChannelID = chanOpenInitDgr.counterpartyChannelID,
                    !.nextSendSeq = 1,
                    !.nextRcvSeq = 1,
                    !.nextAckSeq = 1
                  ])
             ELSE AsChannelEnd([channelEnd EXCEPT 
                    !.state = "INIT",
                    !.channelID = chanOpenInitDgr.channelID,
                    !.counterpartyChannelID = chanOpenInitDgr.counterpartyChannelID
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
    \* get chainID's channel end
    LET channelEnd == chain.connectionEnd.channelEnd IN
    \* get "ChanOpenTry" datagrams, with a valid channel ID
    LET chanOpenTryDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ChanOpenTry"
                            /\ dgr.channelID = GetChannelID(chainID)
                            /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    \* if there are valid "ChanOpenTry" datagrams and the connection is "OPEN", 
    \* update the channel end
    IF /\ chanOpenTryDgrs /= AsSetDatagrams({}) 
       /\ chain.connectionEnd.state = "OPEN" 
    THEN LET chanOpenTryDgr == CHOOSE dgr \in chanOpenTryDgrs : TRUE IN
         LET chanOpenTryChannelEnd == 
             IF channelEnd.order = "ORDERED" 
             THEN AsChannelEnd([channelEnd EXCEPT
                    !.state = "TRYOPEN",
                    !.channelID = chanOpenTryDgr.channelID,
                    !.counterpartyChannelID = chanOpenTryDgr.counterpartyChannelID,
                    !.nextSendSeq = 1,
                    !.nextRcvSeq = 1,
                    !.nextAckSeq = 1
                  ])
             ELSE AsChannelEnd([channelEnd EXCEPT
                    !.state = "TRYOPEN",
                    !.channelID = chanOpenTryDgr.channelID,
                    !.counterpartyChannelID = chanOpenTryDgr.counterpartyChannelID
                  ]) IN 
       
         IF \/ channelEnd.state = "UNINIT"
            \/ /\ channelEnd.state = "INIT" 
               /\ channelEnd.counterpartyChannelID 
                    = chanOpenTryChannelEnd.counterpartyChannelID
         \* if the channel end on the chain is in "UNINIT" or it is in "INIT",  
         \* but the fields are the same as in the datagram, update the channel end     
         THEN LET chanOpenTryConnectionEnd == AsConnectionEnd([
                  chain.connectionEnd EXCEPT !.channelEnd = chanOpenTryChannelEnd
              ]) IN
              LET chanOpenTryChain == AsChainStore([
                  chain EXCEPT !.connectionEnd = chanOpenTryConnectionEnd
              ]) IN
                 
              chanOpenTryChain

         \* otherwise, do not update the chain store
         ELSE chain
    \* otherwise, do not update the chain store    
    ELSE chain

\* Handle "ChanOpenAck" datagrams
HandleChanOpenAck(chainID, chain, datagrams) ==
    \* get chainID's channel end
    LET channelEnd == chain.connectionEnd.channelEnd IN
    \* get "ChanOpenAck" datagrams, with a valid channel ID
    LET chanOpenAckDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ChanOpenAck"
                            /\ dgr.channelID = GetChannelID(chainID)
                            /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    \* if there are valid "ChanOpenAck" datagrams, update the channel end
    IF /\ chanOpenAckDgrs /= AsSetDatagrams({}) 
       /\ chain.connectionEnd.state = "OPEN"
    THEN \* if the channel end on the chain is in "INIT" or it is in "TRYOPEN",   
         \* update the channel end   
         IF \/ channelEnd.state = "INIT"
            \/ channelEnd.state = "TRYOPEN"
         THEN LET chanOpenAckDgr == CHOOSE dgr \in chanOpenAckDgrs : TRUE IN
              LET chanOpenAckChannelEnd == AsChannelEnd([
                  channelEnd EXCEPT 
                    !.state = "OPEN",
                    !.channelID = chanOpenAckDgr.channelID
              ]) IN
              LET chanOpenAckConnectionEnd == AsConnectionEnd([ 
                  chain.connectionEnd EXCEPT !.channelEnd = chanOpenAckChannelEnd
              ]) IN
              LET chanOpenAckChain == AsChainStore([
                  chain EXCEPT !.connectionEnd = chanOpenAckConnectionEnd
              ]) IN
              
              chanOpenAckChain

         \* otherwise, do not update the chain store
         ELSE chain
    \* otherwise, do not update the chain store     
    ELSE chain
    

\* Handle "ChanOpenConfirm" datagrams
HandleChanOpenConfirm(chainID, chain, datagrams) ==
    \* get chainID's channel end
    LET channelEnd == chain.connectionEnd.channelEnd IN
    \* get "ChanOpenConfirm" datagrams, with a valid channel ID 
    LET chanOpenConfirmDgrs == {dgr \in datagrams : 
                                /\ dgr.type = "ChanOpenConfirm"
                                /\ dgr.channelID = GetChannelID(chainID)
                                /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    \* if there are valid "ChanOpenConfirm" datagrams, update the channel end
    IF /\ chanOpenConfirmDgrs /= AsSetDatagrams({}) 
       /\ chain.connectionEnd.state = "OPEN"
    THEN \* if the channel end on the chain is in "TRYOPEN", update the channel end 
         IF channelEnd.state = "TRYOPEN"
         THEN LET chanOpenConfirmDgr == CHOOSE dgr \in chanOpenConfirmDgrs : TRUE IN
              LET chanOpenConfirmChannelEnd == AsChannelEnd([
                  channelEnd EXCEPT 
                    !.state = "OPEN",
                    !.channelID = chanOpenConfirmDgr.channelID
              ]) IN
              LET chanOpenConfirmConnectionEnd == AsConnectionEnd([ 
                  chain.connectionEnd EXCEPT !.channelEnd = chanOpenConfirmChannelEnd
              ]) IN
              LET chanOpenConfirmChain == AsChainStore([
                  chain EXCEPT !.connectionEnd = chanOpenConfirmConnectionEnd
              ]) IN
                 
              chanOpenConfirmChain
         \* otherwise, do not update the chain store
         
         ELSE chain
    \* otherwise, do not update the chain store
    ELSE chain
    
\* Handle "ChanCloseInit" datagrams
HandleChanCloseInit(chainID, chain, datagrams) ==
    \* get chainID's channel end
    LET channelEnd == chain.connectionEnd.channelEnd IN
    \* get "ChanCloseInit" datagrams, with a valid channel ID 
    LET chanCloseInitDgrs == {dgr \in datagrams : 
                              /\ dgr.type = "ChanCloseInit"
                              /\ dgr.channelID = GetChannelID(chainID)} IN
    
    \* if there are valid "ChanCloseInit" datagrams
    IF /\ chanCloseInitDgrs /= AsSetDatagrams({})
    \* and the channel end is neither UNINIT nor CLOSED
       /\ channelEnd.state \notin {"UNINIT", "CLOSED"}
    \* and the connection end is OPEN   
       /\ chain.connectionEnd.state = "OPEN"
    THEN \* then close the channel end
         LET chanCloseInitChannelEnd == AsChannelEnd([
             channelEnd EXCEPT !.state = "CLOSED"
         ]) IN
         LET chanCloseInitConnectionEnd == AsConnectionEnd([ 
             chain.connectionEnd EXCEPT !.channelEnd = chanCloseInitChannelEnd
         ]) IN
         LET chanCloseInitChain == AsChainStore([
             chain EXCEPT !.connectionEnd = chanCloseInitConnectionEnd
         ]) IN
         
         chanCloseInitChain
    \* otherwise, do not update the chain store
    ELSE chain

\* Handle "ChanCloseConfirm" datagrams
HandleChanCloseConfirm(chainID, chain, datagrams) ==
    \* get chainID's channel end
    LET channelEnd == chain.connectionEnd.channelEnd IN
    \* get "ChanCloseConfirm" datagrams, with a valid channel ID 
    LET chanCloseConfirmDgrs == {dgr \in datagrams : 
                              /\ dgr.type = "ChanCloseConfirm"
                              /\ dgr.channelID = GetChannelID(chainID)
                              /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    \* if there are valid "ChanCloseConfirm" datagrams
    IF /\ chanCloseConfirmDgrs /= AsSetDatagrams({})
    \* and the channel end is neither UNINIT nor CLOSED
       /\ channelEnd.state \notin {"UNINIT", "CLOSED"}
    \* and the connection end is OPEN   
       /\ chain.connectionEnd.state = "OPEN"
    THEN \* then close the channel end
         LET chanCloseConfirmChannelEnd == AsChannelEnd([
             channelEnd EXCEPT !.state = "CLOSED"
         ]) IN
         LET chanCloseConfirmConnectionEnd == AsConnectionEnd([ 
             chain.connectionEnd EXCEPT !.channelEnd = chanCloseConfirmChannelEnd
         ]) IN
         LET chanCloseConfirmChain == AsChainStore([
             chain EXCEPT !.connectionEnd = chanCloseConfirmConnectionEnd
         ]) IN
         
         chanCloseConfirmChain
    \* otherwise, do not update the chain store
    ELSE chain

=============================================================================
\* Modification History
\* Last modified Wed Sep 09 14:21:15 CEST 2020 by ilinastoilkovska
\* Created Tue Apr 07 16:58:02 CEST 2020 by ilinastoilkovska
