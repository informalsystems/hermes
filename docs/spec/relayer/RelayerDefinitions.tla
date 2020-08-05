------------------------- MODULE RelayerDefinitions -------------------------

(***************************************************************************
 This module contains definitions of operators that are shared between the 
 different modules
 ***************************************************************************)

EXTENDS Integers, FiniteSets

ChainIDs == {"chainA", "chainB"}
ClientIDs == {"clA", "clB"}
ConnectionIDs == {"connAtoB", "connBtoA"}
ChannelIDs == {"chanAtoB", "chanBtoA"}

nullHeight == 0
nullClientID == "none"
nullConnectionID == "none"
nullChannelID == "none"

ConnectionStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN"}
ChannelStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN", "CLOSED"}
ChannelOrder == {"ORDERED", "UNORDERED"}

Max(S) == CHOOSE x \in S: \A y \in S: y <= x

(********************* TYPE ANNOTATIONS FOR APALACHE **************************)
\* operator for type annotations
a <: b == a

\* unordered channel end type
UnorderedChannelEnd == [state |-> STRING, order |-> STRING, 
                        channelID |-> STRING, counterpartychannelID |-> STRING]
\* ordered channel end type
OrderedChannelEnd == [state |-> STRING, order |-> STRING, 
                      channelID |-> STRING, counterpartychannelID |-> STRING, 
                      nextSendSeq |-> Int, nextRcveq |-> Int, nextAckSeq |-> Int]
                      


(******************************* ChannelEnds *******************************
    A set of channel end records. 
    A channel end record contains the following fields:
    
    - state -- a string 
      Stores the current state of this channel end. It has one of the 
      following values: "UNINIT", "INIT", "TRYOPEN", "OPEN", "CLOSED".
      
    - order -- a string
      Stores whether the channel end is ordered or unordered. It has one of the 
      following values: "UNORDERED", "ORDERED"
        
        * ordered channels have three additional packet sequence fields:
           nextSendSeq -- stores the sequence number of the next packet that is going to be sent,
           nextRcvSeq -- stores the sequence number of the next packet that is going to be received,
           nextAckSeq -- stores the sequence number of the next packet that is going to be acknowledged
      
    - channelID -- a channel identifier
      Stores the channel identifier of this channel end.  
    
    - counterpartyChannelID -- a channel identifier
      Stores the channel identifier of the counterparty channel end. 
 ***************************************************************************)   
ChannelEnds(channelOrdering, maxPacketSeq) ==
    IF channelOrdering = "UNORDERED"
    THEN \* set of unordered channels
         [
             state : ChannelStates,
             order : {"UNORDERED"}, 
             channelID : ChannelIDs \union {nullChannelID},
             counterpartyChannelID : ChannelIDs \union {nullChannelID}
         ] 
    ELSE \* set of ordered channels
         [
             state : ChannelStates,
             order : {"ORDERED"},
             nextSendSeq : 0..maxPacketSeq,
             nextRcvSeq : 0..maxPacketSeq,
             nextAckSeq : 0..maxPacketSeq, 
             channelID : ChannelIDs \union {nullChannelID},
             counterpartyChannelID : ChannelIDs \union {nullChannelID}
         ]
    
(**************************** PacketCommitments ****************************
 A set of packet commitments.
 ***************************************************************************)
 PacketCommitments(maxHeight, maxPacketSeq) ==
    [
        channelID : ChannelIDs, 
        sequence : 1..maxPacketSeq, 
        timeoutHeight : 1..maxHeight
    ]    

(***************************** ConnectionEnds *****************************
    A set of connection end records. 
    A connection end record contains the following fields:
    
    - state -- a string 
      Stores the current state of this connection end. It has one of the 
      following values: "UNINIT", "INIT", "TRYOPEN", "OPEN".
    
    - connectionID -- a connection identifier
      Stores the connection identifier of this connection end.
    
    - counterpartyConnectionID -- a connection identifier
      Stores the connection identifier of the counterparty connection end.
    
    - clientID -- a client identifier
      Stores the client identifier associated with this connection end. 
      
    - counterpartyClientID -- a client identifier
      Stores the counterparty client identifier associated with this connection end.
      
    - channelEnd : a channel end record 
      Stores data about the channel associated with this connection end.  
 ***************************************************************************)
ConnectionEnds(channelOrdering, maxPacketSeq) ==
    [
        state : ConnectionStates,
        connectionID : ConnectionIDs \union {nullConnectionID},
        clientID : ClientIDs \union {nullClientID},
        counterpartyConnectionID : ConnectionIDs \union {nullConnectionID},
        counterpartyClientID : ClientIDs \union {nullClientID}, 
        channelEnd : ChannelEnds(channelOrdering, maxPacketSeq)
    ]  

(******************************** ChainStores ******************************
    A set of chain records. 
    A chain record contains the following fields:
    
    - height : an integer between nullHeight and MaxHeight. 
      Stores the current height of the chain.
    
    - counterpartyClientHeights : a set of integers between 1 and MaxHeight
      Stores the heights of the client for the counterparty chain.

    - connectionEnd : a connection end record 
      Stores data about the connection with the counterparty chain
 ***************************************************************************)
ChainStores(maxHeight, channelOrdering, maxPacketSeq) ==    
    [
        height : 1..maxHeight,
        counterpartyClientHeights : SUBSET(1..maxHeight),
        connectionEnd : ConnectionEnds(channelOrdering, maxPacketSeq),
        packetCommitment : SUBSET(PacketCommitments(maxHeight, maxPacketSeq))
    ]

(********************************* Packets *********************************
 A set of packets.
 ***************************************************************************)
Packets(maxHeight, maxPacketSeq) ==
    [
        sequence : 1..maxPacketSeq,
        timeoutHeight : 1..maxHeight,
        srcChannelID : ChannelIDs,
        dstChannelID : ChannelIDs
    ]

(******************************** Datagrams ********************************
 A set of datagrams.
 ***************************************************************************)
Datagrams(maxHeight, maxPacketSeq) ==
    [type : {"CreateClient"}, clientID : ClientIDs, height : 1..maxHeight]
    \union
    [type : {"ClientUpdate"}, clientID : ClientIDs, height : 1..maxHeight]   
    \union
    [type : {"ConnOpenInit"}, connectionID : ConnectionIDs, clientID : ClientIDs, 
     counterpartyConnectionID : ConnectionIDs, counterpartyClientID : ClientIDs]
    \union
    [type : {"ConnOpenTry"}, desiredConnectionID : ConnectionIDs, 
     counterpartyConnectionID : ConnectionIDs, counterpartyClientID : ClientIDs, 
     clientID : ClientIDs, proofHeight : 1..maxHeight, consensusHeight : 1..maxHeight]
    \union
    [type : {"ConnOpenAck"}, connectionID : ConnectionIDs, proofHeight : 1..maxHeight, 
     consensusHeight : 1..maxHeight ]
    \union
    [type : {"ConnOpenConfirm"}, connectionID : ConnectionIDs, proofHeight : 1..maxHeight] 
    \union
    [type : {"ChanOpenInit"}, channelID : ChannelIDs, counterpartyChannelID : ChannelIDs] 
    \union 
    [type : {"ChanOpenTry"}, channelID : ChannelIDs, counterpartyChannelID : ChannelIDs, 
     proofHeight : 1..maxHeight]
    \union 
    [type : {"ChanOpenAck"}, channelID : ChannelIDs, proofHeight : 1..maxHeight]
    \union
    [type : {"ChanOpenConfirm"}, channelID : ChannelIDs, proofHeight : 1..maxHeight]
    \union 
    [type : {"ChanCloseInit"}, channelID : ChannelIDs]
    \union 
    [type : {"ChanCloseConfirm"}, channelID : ChannelIDs, proofHeight : 1..maxHeight]
    \union 
    [type : {"PacketRecv"}, packet : Packets(maxHeight, maxPacketSeq), proofHeight : 1..maxHeight]
    \union 
    [type : {"PacketAck"}, packet : Packets(maxHeight, maxPacketSeq), acknowledgement : BOOLEAN, proofHeight : 1..maxHeight]

Histories ==
    [
        connInit : BOOLEAN,
        connTryOpen : BOOLEAN, 
        connOpen : BOOLEAN,
        chanInit : BOOLEAN,
        chanTryOpen : BOOLEAN,
        chanOpen : BOOLEAN,
        chanClosed : BOOLEAN
     ] 

(***************************************************************************
 Initial values of a channel end, connection end, chain
 ***************************************************************************)
\* Initial value of an unordered channel end:
\*      - state is "UNINIT"
\*      - order is "UNORDERED"
\*      - channelID, counterpartyChannelID are uninitialized
InitUnorderedChannelEnd ==
    [state |-> "UNINIT",
     order |-> "UNORDERED",
     channelID |-> nullChannelID,
     counterpartyChannelID |-> nullChannelID] <: UnorderedChannelEnd
     
\* Initial value of an ordered channel end:
\*      - state is "UNINIT"
\*      - order is "ORDERED"
\*      - nextSendSeq, nextRcvSeq, nextAckSeq are set to 0
\*      - channelID, counterpartyChannelID are uninitialized
InitOrderedChannelEnd ==
    [state |-> "UNINIT",
     order |-> "ORDERED",
     nextSendSeq |-> 0,
     nextRcvSeq |-> 0,
     nextAckSeq |-> 0,
     channelID |-> nullChannelID,
     counterpartyChannelID |-> nullChannelID] <: OrderedChannelEnd

\* Initial value of a connection end:
\*      - state is "UNINIT"
\*      - connectionID, counterpartyConnectionID are uninitialized
\*      - clientID, counterpartyClientID are uninitialized    
\*      - channelEnd is initialized based on channelOrdering
InitOrderedConnectionEnd ==
    [state |-> "UNINIT",
          connectionID |-> nullConnectionID,
          clientID |-> nullClientID,
          counterpartyConnectionID |-> nullConnectionID,
          counterpartyClientID |-> nullClientID,
          channelEnd |-> InitOrderedChannelEnd]
InitUnorderedConnectionEnd ==
    [state |-> "UNINIT",
          connectionID |-> nullConnectionID,
          clientID |-> nullClientID,
          counterpartyConnectionID |-> nullConnectionID,
          counterpartyClientID |-> nullClientID,
          channelEnd |-> InitUnorderedChannelEnd]  

\* Initial value of the chain store: 
\*      - height is initialized to 1
\*      - the counterparty light client is uninitialized
\*      - the connection end is initialized to InitConnectionEnd 
InitOrderedChainStore ==
    [height |-> 1,
     counterpartyClientHeights |-> {}, 
     connectionEnd |-> InitOrderedConnectionEnd,
     packetCommitment |-> {}]

InitUnorderedChainStore ==
    [height |-> 1,
     counterpartyClientHeights |-> {}, 
     connectionEnd |-> InitUnorderedConnectionEnd,
     packetCommitment |-> {}]

\* Initial value of history flags         
InitHistory ==
     [
        connInit |-> FALSE,
        connTryOpen |-> FALSE, 
        connOpen |-> FALSE,
        chanInit |-> FALSE,
        chanTryOpen |-> FALSE,
        chanOpen |-> FALSE,
        chanClosed |-> FALSE
     ]    
         
(***************************************************************************
 Client helper operators
 ***************************************************************************)

\* get the ID of chainID's counterparty chain    
GetCounterpartyChainID(chainID) ==
    IF chainID = "chainA" THEN "chainB" ELSE "chainA"    
 
\* get the client ID of the client for chainID 
GetClientID(chainID) ==
    IF chainID = "chainA" THEN "clA" ELSE "clB"
        
\* get the client ID of the client for chainID's counterparty chain           
GetCounterpartyClientID(chainID) ==
    IF chainID = "chainA" THEN "clB" ELSE "clA"
    
\* get the latest height of chainID
GetLatestHeight(chain) ==
    chain.height   
      
\* get the maximal height of the client for chainID's counterparty chain    
GetMaxCounterpartyClientHeight(chain) ==
    IF chain.counterpartyClientHeights /= {}
    THEN Max(chain.counterpartyClientHeights)
    ELSE nullHeight

\* get the set of heights of the client for chainID's counterparty chain    
GetCounterpartyClientHeights(chain) ==
    chain.counterpartyClientHeights        

\* returns true if the counterparty client is initialized on chainID
IsCounterpartyClientOnChain(chain) ==
    chain.counterpartyClientHeights /= {}

\* returns true if the height h is in counterparty client heights on chainID 
IsCounterpartyClientHeightOnChain(chain, h) ==
    h \in chain.counterpartyClientHeights
     
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
\* get the connection end at chainID
GetConnectionEnd(chain) == 
    chain.connectionEnd

\* returns true if the connection end on chainID is UNINIT
IsConnectionUninit(chain) ==
    chain.connectionEnd.state = "UNINIT"

\* returns true if the connection end on chainID is INIT
IsConnectionInit(chain) ==
    chain.connectionEnd.state = "INIT"

\* returns true if the connection end on chainID is TRYOPEN
IsConnectionTryOpen(chain) ==
    chain.connectionEnd.state = "TRYOPEN"
    
\* returns true if the connection end on chainID is OPEN
IsConnectionOpen(chain) ==
    chain.connectionEnd.state = "OPEN"
          
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
                   
\* get the channel end at the connection end of chainID          
GetChannelEnd(chain) ==
    chain.connectionEnd.channelEnd
    
\* returns true if the channel end on chainID is UNINIT
IsChannelUninit(chain) ==
    chain.connectionEnd.channelEnd.state = "UNINIT"

\* returns true if the channel end on chainID is INIT
IsChannelInit(chain) ==
    chain.connectionEnd.channelEnd.state = "INIT"

\* returns true if the channel end on chainID is TRYOPEN
IsChannelTryOpen(chain) ==
    chain.connectionEnd.channelEnd.state = "TRYOPEN"
    
\* returns true if the channel end on chainID is OPEN
IsChannelOpen(chain) ==
    chain.connectionEnd.channelEnd.state = "OPEN"    
    
\* returns true if the channel end on chainID is CLOSED
IsChannelClosed(chain) ==
    chain.connectionEnd.channelEnd.state = "CLOSED"     

=============================================================================
\* Modification History
\* Last modified Wed Aug 05 12:39:33 CEST 2020 by ilinastoilkovska
\* Created Fri Jun 05 16:56:21 CET 2020 by ilinastoilkovska