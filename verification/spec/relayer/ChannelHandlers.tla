-------------------------- MODULE ChannelHandlers --------------------------

(***************************************************************************
 This module contains definitions of operators that are used to handle
 channel datagrams
 ***************************************************************************)

EXTENDS Naturals, FiniteSets

ChannelIDs == {"chanAtoB", "chanBtoA"}
nullChannelID == "none"

ChannelStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN", "CLOSED"}
ChannelOrder == {"ORDERED", "UNORDERED"}

(***************************************************************************
 Channel helper operators
 ***************************************************************************)

\* get the channel ID of the channel end at the connection end of chainID
GetChannelID(chainID) ==
    IF chainID = "chainA"
    THEN "chanAtoB"
    ELSE IF chainID = "chainB"
         THEN "chanBtoA"
         ELSE nullChannelID
         
\* get the channel ID of the channel end at chainID's counterparty chain
GetCounterpartyChannelID(chainID) ==
    IF chainID = "chainA"
    THEN "chanBtoA"
    ELSE IF chainID = "chainB"
         THEN "chanAtoB"
         ELSE nullChannelID          

(***************************************************************************
 Channel datagram handlers
 ***************************************************************************)
 
\* Handle "ChanOpenInit" datagrams
HandleChanOpenInit(chainID, chain, datagrams) ==
    \* get "ChanOpenInit" datagrams, with a valid channel ID
    LET chanOpenInitDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ChanOpenInit"
                            /\ dgr.channelID = GetChannelID(chainID)} IN
    
    IF chanOpenInitDgrs /= {} /\ chain.connectionEnd.state /= "UNINIT"
    \* if there are valid "ChanOpenInit" datagrams and the connection is not "UNINIT", 
    \* create a new channel end and update the chain
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
        
         \* TODO: check here if channel is already in INIT?
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
    
    IF chanOpenTryDgrs /= {} /\ chain.connectionEnd.state = "OPEN"
    \* if there are valid "ChanOpenTry" datagrams and the connection is "OPEN", 
    \* update the channel end 
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
    
    IF chanOpenAckDgrs /= {} /\ chain.connectionEnd.state = "OPEN"
    \* if there are valid "ChanOpenAck" datagrams, update the channel end 
    THEN IF \/ chain.connectionEnd.channelEnd.state = "INIT"
            \/ chain.connectionEnd.channelEnd.state = "TRYOPEN"
         \* if the channel end on the chain is in "INIT" or it is in "TRYOPEN",   
         \* update the channel end       
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
    
    IF chanOpenConfirmDgrs /= {} /\ chain.connectionEnd.state = "OPEN"
    \* if there are valid "ChanOpenConfirm" datagrams, update the channel end 
    THEN IF chain.connectionEnd.channelEnd.state = "TRYOPEN"
         \* if the channel end on the chain is in "TRYOPEN", update the channel end       
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
 
=============================================================================
\* Modification History
\* Last modified Thu May 14 16:29:29 CEST 2020 by ilinastoilkovska
\* Created Tue Apr 07 16:58:02 CEST 2020 by ilinastoilkovska
