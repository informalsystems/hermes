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
HandleChanOpenInit(chainID, chain, history, datagrams) ==
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
         \* update history variable
         LET chanOpenInitHistory == AsHistory([
             history EXCEPT !.chanInit = TRUE
         ]) IN
                 
         [store |-> AsChainStore(chanOpenInitChain), 
          history |-> AsHistory(chanOpenInitHistory)]
    \* otherwise, do not update the chain     
    ELSE [store |-> AsChainStore(chain), history |-> AsHistory(history)]

\* Handle "ChanOpenTry" datagrams
HandleChanOpenTry(chainID, chain, history, datagrams) ==
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
              
              \* update history variable
              LET chanOpenTryHistory == AsHistory([
                  history EXCEPT !.chanTryOpen = TRUE
              ]) IN
                 
              [store |-> AsChainStore(chanOpenTryChain), 
               history |-> AsHistory(chanOpenTryHistory)]

         \* otherwise, do not update the chain
         ELSE [store |-> AsChainStore(chain), history |-> AsHistory(history)]
    \* otherwise, do not update the chain     
    ELSE [store |-> AsChainStore(chain), history |-> AsHistory(history)]

\* Handle "ChanOpenAck" datagrams
HandleChanOpenAck(chainID, chain, history, datagrams) ==
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
              
              \* update history variable
              LET chanOpenAckHistory == AsHistory([
                  history EXCEPT !.chanOpen = TRUE
              ]) IN
                 
              [store |-> AsChainStore(chanOpenAckChain), 
               history |-> AsHistory(chanOpenAckHistory)]                
         \* otherwise, do not update the chain
         ELSE [store |-> AsChainStore(chain), history |-> AsHistory(history)]
    \* otherwise, do not update the chain     
    ELSE [store |-> AsChainStore(chain), history |-> AsHistory(history)]
    

\* Handle "ChanOpenConfirm" datagrams
HandleChanOpenConfirm(chainID, chain, history, datagrams) ==
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
              
              \* update history variable
              LET chanOpenConfirmHistory == AsHistory([
                  history EXCEPT !.chanOpen = TRUE
              ]) IN
                 
              [store |-> AsChainStore(chanOpenConfirmChain), 
               history |-> AsHistory(chanOpenConfirmHistory)]                
         \* otherwise, do not update the chain
         ELSE [store |-> AsChainStore(chain), history |-> AsHistory(history)]
    \* otherwise, do not update the chain     
    ELSE [store |-> AsChainStore(chain), history |-> AsHistory(history)] 
    
\* Handle "ChanCloseInit" datagrams
HandleChanCloseInit(chainID, chain, history, datagrams) ==
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
         
         \* update history variable
         LET chanCloseInitHistory == AsHistory([
             history EXCEPT !.chanClosed = TRUE
         ]) IN
         [store |-> AsChainStore(chanCloseInitChain), 
          history |-> AsHistory(chanCloseInitHistory)]              
    \* otherwise, do not update the chain
    ELSE [store |-> AsChainStore(chain), history |-> AsHistory(history)]

\* Handle "ChanCloseConfirm" datagrams
HandleChanCloseConfirm(chainID, chain, history, datagrams) ==
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
         
         \* update history variable
         LET chanCloseConfirmHistory == AsHistory([
             history EXCEPT !.chanClosed = TRUE
         ]) IN
         [store |-> AsChainStore(chanCloseConfirmChain), 
          history |-> AsHistory(chanCloseConfirmHistory)]              
    \* otherwise, do not update the chain
    ELSE [store |-> AsChainStore(chain), history |-> AsHistory(history)]    

=============================================================================
\* Modification History
\* Last modified Mon Aug 10 17:01:30 CEST 2020 by ilinastoilkovska
\* Created Tue Apr 07 16:58:02 CEST 2020 by ilinastoilkovska
