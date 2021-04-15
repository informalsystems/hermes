------------------------ MODULE ICS04ChannelHandlers -----------------------

(***************************************************************************
 This module contains definitions of operators that are used to handle
 channel handshake datagrams.
 ***************************************************************************)

EXTENDS Integers, FiniteSets, IBCCoreDefinitions         

(***************************************************************************
 Channel datagram handlers
 ***************************************************************************)

\* Handle "ChanOpenInit" datagrams
\* @type: (Str, CHAINSTORE, Set(DATAGRAM)) => CHAINSTORE;
HandleChanOpenInit(chainID, chain, datagrams) ==
    \* get chainID's connection end
    LET connectionEnd == GetConnectionEnd(chain) IN
    \* get "ChanOpenInit" datagrams, with a valid port and channel ID
    LET chanOpenInitDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ChanOpenInit"
                            /\ dgr.portID = GetPortID(chainID)
                            /\ dgr.channelID = GetChannelID(chainID)} IN
    
    \* if there are valid "ChanOpenInit" datagrams and the connection is not "UNINIT", 
    \* initialize the channel end and update the chain
    IF /\ chanOpenInitDgrs /= {}
       /\ connectionEnd.state /= "UNINIT" 
       /\ connectionEnd.channelEnd.state = "UNINIT"
    THEN LET chanOpenInitDgr == CHOOSE dgr \in chanOpenInitDgrs : TRUE IN
         LET chanOpenInitChannelEnd == 
             IF connectionEnd.channelEnd.order = "ORDERED" 
             THEN [
                    state |-> "INIT",
                    order |-> "ORDERED",
                    nextSendSeq |-> 1,
                    nextRcvSeq |-> 1,
                    nextAckSeq |-> 1,
                    portID |-> chanOpenInitDgr.portID,
                    channelID |-> chanOpenInitDgr.channelID,
                    counterpartyPortID |-> chanOpenInitDgr.counterpartyPortID,
                    counterpartyChannelID |-> chanOpenInitDgr.counterpartyChannelID
                  ]
             ELSE [ 
                    state |-> "INIT",
                    order |-> "UNORDERED",
                    portID |-> chanOpenInitDgr.portID,
                    channelID |-> chanOpenInitDgr.channelID,
                    counterpartyPortID |-> chanOpenInitDgr.counterpartyPortID,
                    counterpartyChannelID |-> chanOpenInitDgr.counterpartyChannelID
                  ] IN 
         LET chanOpenInitConnectionEnd == [
             chain.connectionEnd EXCEPT !.channelEnd = chanOpenInitChannelEnd
         ] IN
         LET chanOpenInitChain == [
             chain EXCEPT !.connectionEnd = chanOpenInitConnectionEnd            
         ] IN
         
         chanOpenInitChain
    
    \* otherwise, do not update the chain store
    ELSE chain

\* Handle "ChanOpenTry" datagrams
\* @type: (Str, CHAINSTORE, Set(DATAGRAM)) => CHAINSTORE;
HandleChanOpenTry(chainID, chain, datagrams) ==
    \* get chainID's connection end
    LET connectionEnd == GetConnectionEnd(chain) IN
    \* get "ChanOpenTry" datagrams, with a valid port and channel ID
    LET chanOpenTryDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ChanOpenTry"
                            /\ dgr.portID = GetPortID(chainID)
                            /\ dgr.channelID = GetChannelID(chainID)
                            /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    \* if there are valid "ChanOpenTry" datagrams and the connection is "OPEN", 
    \* update the channel end
    IF /\ chanOpenTryDgrs /= {}
       /\ chain.connectionEnd.state = "OPEN" 
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
                THEN [
                        state |-> "TRYOPEN",
                        order |-> "ORDERED",
                        nextSendSeq |-> 1,
                        nextRcvSeq |-> 1,
                        nextAckSeq |-> 1,
                        portID |-> chanOpenTryDgr.portID,
                        channelID |-> chanOpenTryDgr.channelID,
                        counterpartyPortID |-> chanOpenTryDgr.counterpartyPortID,
                        counterpartyChannelID |-> chanOpenTryDgr.counterpartyChannelID
                  ]
                ELSE [
                        state |-> "TRYOPEN",
                        order |-> "UNORDERED",
                        portID |-> chanOpenTryDgr.portID,
                        channelID |-> chanOpenTryDgr.channelID,
                        counterpartyPortID |-> chanOpenTryDgr.counterpartyPortID,
                        counterpartyChannelID |-> chanOpenTryDgr.counterpartyChannelID
                  ] IN 
       
              LET chanOpenTryConnectionEnd == [
                  connectionEnd EXCEPT !.channelEnd = chanOpenTryChannelEnd
              ] IN
              
              LET chanOpenTryChain == [
                  chain EXCEPT !.connectionEnd = chanOpenTryConnectionEnd
              ] IN
                 
              chanOpenTryChain

    \* otherwise, do not update the chain store
         ELSE chain
    ELSE chain

\* Handle "ChanOpenAck" datagrams
\* @type: (Str, CHAINSTORE, Set(DATAGRAM)) => CHAINSTORE;
HandleChanOpenAck(chainID, chain, datagrams) ==
    \* get chainID's connection end
    LET connectionEnd == GetConnectionEnd(chain) IN
    \* get chainID's channel end
    LET channelEnd == GetChannelEnd(chain) IN
    \* get "ChanOpenAck" datagrams, with a valid channel ID
    LET chanOpenAckDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "ChanOpenAck"
                            /\ dgr.portID = channelEnd.portID
                            /\ dgr.channelID = channelEnd.channelID
                            /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    \* if there are valid "ChanOpenAck" datagrams, update the channel end
    IF /\ chanOpenAckDgrs /= {}
       /\ connectionEnd.state = "OPEN"
    THEN \* if the channel end on the chain is in "INIT" or it is in "TRYOPEN",   
         \* update the channel end   
         IF \/ channelEnd.state = "INIT"
            \/ channelEnd.state = "TRYOPEN"
         THEN LET chanOpenAckDgr == CHOOSE dgr \in chanOpenAckDgrs : TRUE IN
              LET chanOpenAckChannelEnd == [
                  channelEnd EXCEPT !.state = "OPEN"
              ] IN
              LET chanOpenAckConnectionEnd == [ 
                  connectionEnd EXCEPT !.channelEnd = chanOpenAckChannelEnd
              ] IN
              LET chanOpenAckChain == [
                  chain EXCEPT !.connectionEnd = chanOpenAckConnectionEnd
              ] IN
              
              chanOpenAckChain

    \* otherwise, do not update the chain store
         ELSE chain
    ELSE chain
    

\* Handle "ChanOpenConfirm" datagrams
\* @type: (Str, CHAINSTORE, Set(DATAGRAM)) => CHAINSTORE;
HandleChanOpenConfirm(chainID, chain, datagrams) ==
    \* get chainID's connection end
    LET connectionEnd == GetConnectionEnd(chain) IN
    \* get chainID's channel end
    LET channelEnd ==  GetChannelEnd(chain) IN
    \* get "ChanOpenConfirm" datagrams, with a valid channel ID 
    LET chanOpenConfirmDgrs == {dgr \in datagrams : 
                                /\ dgr.type = "ChanOpenConfirm"
                                /\ dgr.portID = channelEnd.portID
                                /\ dgr.channelID = channelEnd.channelID
                                /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    \* if there are valid "ChanOpenConfirm" datagrams, update the channel end
    IF /\ chanOpenConfirmDgrs /= {}
       /\ connectionEnd.state = "OPEN"
    THEN \* if the channel end on the chain is in "TRYOPEN", update the channel end 
         IF channelEnd.state = "TRYOPEN"
         THEN LET chanOpenConfirmDgr == CHOOSE dgr \in chanOpenConfirmDgrs : TRUE IN
              LET chanOpenConfirmChannelEnd == [
                  channelEnd EXCEPT !.state = "OPEN"
              ] IN
              LET chanOpenConfirmConnectionEnd == [ 
                  connectionEnd EXCEPT !.channelEnd = chanOpenConfirmChannelEnd
              ] IN
              LET chanOpenConfirmChain == [
                  chain EXCEPT !.connectionEnd = chanOpenConfirmConnectionEnd
              ] IN
                 
              chanOpenConfirmChain

    \* otherwise, do not update the chain store
         ELSE chain
    ELSE chain
    
\* Handle "ChanCloseInit" datagrams
\* @type: (Str, CHAINSTORE, Set(DATAGRAM)) => CHAINSTORE;
HandleChanCloseInit(chainID, chain, datagrams) ==
    \* get chainID's connection end
    LET connectionEnd == GetConnectionEnd(chain) IN
    \* get chainID's channel end
    LET channelEnd == GetChannelEnd(chain) IN
    \* get "ChanCloseInit" datagrams, with a valid channel ID 
    LET chanCloseInitDgrs == {dgr \in datagrams : 
                              /\ dgr.type = "ChanCloseInit"
                              /\ dgr.portID = channelEnd.portID
                              /\ dgr.channelID = channelEnd.channelID} IN
    
    \* if there are valid "ChanCloseInit" datagrams
    IF /\ chanCloseInitDgrs /= {}
    \* and the channel end is neither UNINIT nor CLOSED
       /\ channelEnd.state \notin {"UNINIT", "CLOSED"}
    \* and the connection end is OPEN   
       /\ connectionEnd.state = "OPEN"
    THEN \* then close the channel end
         LET chanCloseInitChannelEnd == [
             channelEnd EXCEPT !.state = "CLOSED"
         ] IN
         LET chanCloseInitConnectionEnd == [ 
             connectionEnd EXCEPT !.channelEnd = chanCloseInitChannelEnd
         ] IN
         LET chanCloseInitChain == [
             chain EXCEPT !.connectionEnd = chanCloseInitConnectionEnd
         ] IN
         
         chanCloseInitChain
    
    \* otherwise, do not update the chain store
    ELSE chain

\* Handle "ChanCloseConfirm" datagrams
\* @type: (Str, CHAINSTORE, Set(DATAGRAM)) => CHAINSTORE;
HandleChanCloseConfirm(chainID, chain, datagrams) ==
    \* get chainID's connection end
    LET connectionEnd == GetConnectionEnd(chain) IN
    \* get chainID's channel end
    LET channelEnd == GetChannelEnd(chain) IN
    \* get "ChanCloseConfirm" datagrams, with a valid channel ID 
    LET chanCloseConfirmDgrs == {dgr \in datagrams : 
                                 /\ dgr.type = "ChanCloseConfirm"
                                 /\ dgr.portID = channelEnd.portID
                                 /\ dgr.channelID = channelEnd.channelID
                                 /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    \* if there are valid "ChanCloseConfirm" datagrams
    IF /\ chanCloseConfirmDgrs /= {}
    \* and the channel end is neither UNINIT nor CLOSED
       /\ channelEnd.state \notin {"UNINIT", "CLOSED"}
    \* and the connection end is OPEN   
       /\ connectionEnd.state = "OPEN"
    THEN \* then close the channel end
         LET chanCloseConfirmChannelEnd == [
             channelEnd EXCEPT !.state = "CLOSED"
         ] IN
         LET chanCloseConfirmConnectionEnd == [ 
             connectionEnd EXCEPT !.channelEnd = chanCloseConfirmChannelEnd
         ] IN
         LET chanCloseConfirmChain == [
             chain EXCEPT !.connectionEnd = chanCloseConfirmConnectionEnd
         ] IN
         
         chanCloseConfirmChain
    
    \* otherwise, do not update the chain store
    ELSE chain

=============================================================================
\* Modification History
\* Last modified Mon Apr 12 14:22:44 CEST 2021 by ilinastoilkovska
\* Created Tue Apr 07 16:58:02 CEST 2020 by ilinastoilkovska
