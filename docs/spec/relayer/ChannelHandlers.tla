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
    \* get "ChanOpenInit" datagrams, with a valid channel ID
    LET chanOpenInitDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ChanOpenInit"
                            /\ dgr.channelID = GetChannelID(chainID)} IN
    
    \* if there are valid "ChanOpenInit" datagrams and the connection is not "UNINIT", 
    \* create a new channel end and update the chain
    IF chanOpenInitDgrs /= {} /\ chain.connectionEnd.state /= "UNINIT" 
                              /\ chain.connectionEnd.channelEnd.state = "UNINIT"
    THEN LET chanOpenInitDgr == CHOOSE dgr \in chanOpenInitDgrs : TRUE IN
         LET chanOpenInitChannelEnd == [
             state |-> "INIT",
             channelID |-> chanOpenInitDgr.channelID,
             counterpartyChannelID |-> chanOpenInitDgr.counterpartyChannelID
         ] IN 
         LET chanOpenInitConnectionEnd == [
             chain.connectionEnd EXCEPT !.channelEnd = chanOpenInitChannelEnd
         ] IN
         LET chanOpenInitChain == [
            chain EXCEPT !.connectionEnd = chanOpenInitConnectionEnd            
         ] IN
        
         \* TODO: when handling packets later on, set nextSequenceRecv and nextSequenceSend to 1
         chanOpenInitChain
    \* otherwise, do not update the chain     
    ELSE chain

\* Handle "ChanOpenTry" datagrams
HandleChanOpenTry(chainID, chain, datagrams) ==
    \* get "ChanOpenTry" datagrams, with a valid channel ID
    LET chanOpenTryDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ChanOpenTry"
                            /\ dgr.channelID = GetChannelID(chainID)
                            /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    \* if there are valid "ChanOpenTry" datagrams and the connection is "OPEN", 
    \* update the channel end
    IF chanOpenTryDgrs /= {} /\ chain.connectionEnd.state = "OPEN" 
    THEN LET chanOpenTryDgr == CHOOSE dgr \in chanOpenTryDgrs : TRUE IN
         LET chanOpenTryChannelEnd == [
             state |-> "TRYOPEN",
             channelID |-> chanOpenTryDgr.channelID,
             counterpartyChannelID |-> chanOpenTryDgr.counterpartyChannelID
            ] IN 
       
         IF \/ chain.connectionEnd.channelEnd.state = "UNINIT"
            \/ /\ chain.connectionEnd.channelEnd.state = "INIT" 
               /\ chain.connectionEnd.channelEnd.counterpartyChannelID 
                    = chanOpenTryChannelEnd.counterpartyChannelID
         \* if the channel end on the chain is in "UNINIT" or it is in "INIT",  
         \* but the fields are the same as in the datagram, update the channel end     
         THEN LET chanOpenTryConnectionEnd == [
                  chain.connectionEnd EXCEPT !.channelEnd = chanOpenTryChannelEnd
              ] IN
              LET chanOpenTryChain == [
                  chain EXCEPT !.connectionEnd = chanOpenTryConnectionEnd
              ] IN
                
              chanOpenTryChain
         \* otherwise, do not update the chain
         ELSE chain
    \* otherwise, do not update the chain     
    ELSE chain

\* Handle "ChanOpenAck" datagrams
HandleChanOpenAck(chainID, chain, datagrams) ==
    \* get "ChanOpenAck" datagrams, with a valid channel ID
    LET chanOpenAckDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ChanOpenAck"
                            /\ dgr.channelID = GetChannelID(chainID)
                            /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    \* if there are valid "ChanOpenAck" datagrams, update the channel end
    IF chanOpenAckDgrs /= {} /\ chain.connectionEnd.state = "OPEN"
    THEN \* if the channel end on the chain is in "INIT" or it is in "TRYOPEN",   
         \* update the channel end   
         IF \/ chain.connectionEnd.channelEnd.state = "INIT"
            \/ chain.connectionEnd.channelEnd.state = "TRYOPEN"
         THEN LET chanOpenAckDgr == CHOOSE dgr \in chanOpenAckDgrs : TRUE IN
              LET chanOpenAckChannelEnd == [
                  chain.connectionEnd.channelEnd EXCEPT !.state = "OPEN",
                                                        !.channelID = chanOpenAckDgr.channelID
              ] IN
              LET chanOpenAckConnectionEnd == [ 
                  chain.connectionEnd EXCEPT !.channelEnd = chanOpenAckChannelEnd
                ] IN
              LET chanOpenAckChain == [
                  chain EXCEPT !.connectionEnd = chanOpenAckConnectionEnd
                ] IN
              
              chanOpenAckChain                
         \* otherwise, do not update the chain
         ELSE chain
    \* otherwise, do not update the chain     
    ELSE chain
    

\* Handle "ChanOpenConfirm" datagrams
HandleChanOpenConfirm(chainID, chain, datagrams) ==
    \* get "ChanOpenConfirm" datagrams, with a valid channel ID 
    LET chanOpenConfirmDgrs == {dgr \in datagrams : 
                                /\ dgr.type = "ChanOpenConfirm"
                                /\ dgr.channelID = GetChannelID(chainID)
                                /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    \* if there are valid "ChanOpenConfirm" datagrams, update the channel end
    IF chanOpenConfirmDgrs /= {} /\ chain.connectionEnd.state = "OPEN"
    THEN \* if the channel end on the chain is in "TRYOPEN", update the channel end 
         IF chain.connectionEnd.channelEnd.state = "TRYOPEN"
         THEN LET chanOpenConfirmDgr == CHOOSE dgr \in chanOpenConfirmDgrs : TRUE IN
              LET chanOpenConfirmChannelEnd == [
                  chain.connectionEnd.channelEnd EXCEPT !.state = "OPEN",
                                                        !.channelID = chanOpenConfirmDgr.channelID
              ] IN
              LET chanOpenConfirmConnectionEnd == [ 
                  chain.connectionEnd EXCEPT !.channelEnd = chanOpenConfirmChannelEnd
              ] IN
              LET chanOpenConfirmChain == [
                  chain EXCEPT !.connectionEnd = chanOpenConfirmConnectionEnd
              ] IN
              
              chanOpenConfirmChain                
         \* otherwise, do not update the chain
         ELSE chain
    \* otherwise, do not update the chain     
    ELSE chain 
    
\* Handle "ChanCloseInit" datagrams
HandleChanCloseInit(chainID, chain, datagrams) ==
    \* get "ChanCloseInit" datagrams, with a valid channel ID 
    LET chanCloseInitDgrs == {dgr \in datagrams : 
                              /\ dgr.type = "ChanCloseInit"
                              /\ dgr.channelID = GetChannelID(chainID)} IN
    
    \* if there are valid "ChanCloseInit" datagrams
    IF /\ chanCloseInitDgrs /= {} 
    \* and the channel end is neither UNINIT nor CLOSED
       /\ chain.connectionEnd.channelEnd.state \notin {"UNINIT", "CLOSED"}
    \* and the connection end is OPEN   
       /\ chain.connectionEnd.state = "OPEN"
    THEN \* then close the channel end
         LET chanCloseInitChannelEnd == [
             chain.connectionEnd.channelEnd EXCEPT !.state = "CLOSED"
         ] IN
         LET chanCloseInitConnectionEnd == [ 
             chain.connectionEnd EXCEPT !.channelEnd = chanCloseInitChannelEnd
         ] IN
         LET chanCloseInitChain == [
             chain EXCEPT !.connectionEnd = chanCloseInitConnectionEnd
         ] IN
         
         chanCloseInitChain              
    \* otherwise, do not update the chain
    ELSE chain

\* Handle "ChanCloseConfirm" datagrams
HandleChanCloseConfirm(chainID, chain, datagrams) ==
    \* get "ChanCloseConfirm" datagrams, with a valid channel ID 
    LET chanCloseConfirmDgrs == {dgr \in datagrams : 
                              /\ dgr.type = "ChanCloseConfirm"
                              /\ dgr.channelID = GetChannelID(chainID)
                              /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    \* if there are valid "ChanCloseConfirm" datagrams
    IF /\ chanCloseConfirmDgrs /= {} 
    \* and the channel end is neither UNINIT nor CLOSED
       /\ chain.connectionEnd.channelEnd.state \notin {"UNINIT", "CLOSED"}
    \* and the connection end is OPEN   
       /\ chain.connectionEnd.state = "OPEN"
    THEN \* then close the channel end
         LET chanCloseInitChannelEnd == [
             chain.connectionEnd.channelEnd EXCEPT !.state = "CLOSED"
         ] IN
         LET chanCloseInitConnectionEnd == [ 
             chain.connectionEnd EXCEPT !.channelEnd = chanCloseInitChannelEnd
         ] IN
         LET chanCloseInitChain == [
             chain EXCEPT !.connectionEnd = chanCloseInitConnectionEnd
         ] IN
         
         chanCloseInitChain              
    \* otherwise, do not update the chain
    ELSE chain    

=============================================================================
\* Modification History
\* Last modified Thu Jul 09 09:13:10 CEST 2020 by ilinastoilkovska
\* Created Tue Apr 07 16:58:02 CEST 2020 by ilinastoilkovska
