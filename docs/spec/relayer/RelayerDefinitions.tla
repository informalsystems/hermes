------------------------- MODULE RelayerDefinitions -------------------------

(***************************************************************************
 This module contains definitions of operators that are shared between the 
 different modules
 ***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences

(********************* TYPE ANNOTATIONS FOR APALACHE ***********************)
\* operator for type annotations
a <: b == a

\* unordered channel end type
UnorderedChannelEndType == 
    [
        state |-> STRING, 
        order |-> STRING, 
        channelID |-> STRING, 
        counterpartyChannelID |-> STRING
    ]
    
\* ordered channel end type
OrderedChannelEndType == 
    [
        state |-> STRING, 
        order |-> STRING, 
        channelID |-> STRING, 
        counterpartyChannelID |-> STRING,
        nextSendSeq |-> Int, 
        nextRcvSeq |-> Int, 
        nextAckSeq |-> Int
    ]

\* to deal with union types, use the supertype    
ChannelEndType == OrderedChannelEndType    
       
\* connection end type
ConnectionEndType == 
    [
        state |-> STRING, 
        connectionID |-> STRING, 
        clientID |-> STRING,
        counterpartyConnectionID |-> STRING, 
        counterpartyClientID |-> STRING,
        channelEnd |-> ChannelEndType
    ]

\* packet commitment type
PacketCommitmentType == 
    [
        channelID |-> STRING, 
        sequence |-> Int, 
        timeoutHeight |-> Int
    ]
   
\* packet receipt type
PacketReceiptType ==
    [
        channelID |-> STRING, 
        sequence |-> Int 
    ]    

\* packet acknowledgement type
PacketAcknowledgementType ==
    [
        channelID |-> STRING, 
        sequence |-> Int,
        acknowledgement |-> BOOLEAN
    ]

\* packet type
PacketType ==
    [
        sequence |-> Int,
        timeoutHeight |-> Int, 
        srcChainID |-> STRING,
        dstChainID |-> STRING
    ]
    
\* packet log entry type    
PacketLogEntryType ==
    [
        type |-> STRING,
        srcChainID |-> STRING,
        sequence |-> Int,
        timeoutHeight |-> Int,
        acknowledgement |-> BOOLEAN
    ]
        

\* chain store type 
ChainStoreType == 
    [
        height |-> Int, 
        counterpartyClientHeights |-> {Int},
        connectionEnd |-> ConnectionEndType, 
        packetCommitments |-> {PacketCommitmentType},
        packetsToAcknowledge |-> Seq(PacketType),
        packetReceipts |-> {PacketReceiptType},
        packetAcknowledgements |-> {PacketAcknowledgementType} 
    ]

\* history variable type
HistoryType == 
    [
        connInit |-> BOOLEAN, 
        connTryOpen |-> BOOLEAN, 
        connOpen |-> BOOLEAN,
        chanInit |-> BOOLEAN, 
        chanTryOpen |-> BOOLEAN, 
        chanOpen |-> BOOLEAN, 
        chanClosed |-> BOOLEAN
    ]

\* client datagram type
ClientDatagramType ==
    [
        type |-> STRING,
        clientID |-> STRING,
        height |-> Int   
    ]

\* connection datagram type
ConnectionDatagramType ==
    [
        type |-> STRING,
        connectionID |-> STRING,
        clientID |-> STRING,
        counterpartyConnectionID |-> STRING,
        counterpartyClientID |-> STRING,
        proofHeight |-> Int,
        consensusHeight |-> Int
    ]

\* channel datagram type
ChannelDatagramType ==
    [
        type |-> STRING,
        channelID |-> STRING,
        counterpartyChannelID |-> STRING,
        proofHeight |-> Int
    ]

\* packet datagram type
PacketDatagramType ==
    [
        type |-> STRING,
        packet |-> PacketType,
        acknowledgement |-> BOOLEAN,
        proofHeight |-> Int
    ]

\* datagram type (record type containing fields of all datagrams)                  
DatagramType ==
    [
        type |-> STRING,
        height |-> Int,
        proofHeight |-> Int,
        consensusHeight |-> Int,
        clientID |-> STRING,
        counterpartyClientID |-> STRING,
        connectionID |-> STRING,
        counterpartyConnectionID |-> STRING,
        channelID |-> STRING,
        counterpartyChannelID |-> STRING,
        packet |-> PacketType,
        acknowledgement |-> BOOLEAN
    ]

AsID(ID) == ID <: STRING
AsInt(n) == n <: Int
AsSetInt(S) == S <: {Int}
AsString(s) == s <: STRING

AsChannelEnd(channelEnd) == channelEnd <: ChannelEndType
AsSetChannelEnd(CE) == CE <: {ChannelEndType}

AsConnectionEnd(connectionEnd) == connectionEnd <: ConnectionEndType  

AsChainStore(chainStore) == chainStore <: ChainStoreType

AsHistory(history) == history <: HistoryType

AsDatagram(dgr) == dgr <: DatagramType

AsClientDatagram(dgr) == dgr <: ClientDatagramType
AsSetClientDatagrams(Dgrs) == Dgrs <: {ClientDatagramType}

AsConnectionDatagram(dgr) == dgr <: ConnectionDatagramType
AsSetConnectionDatagrams(Dgrs) == Dgrs <: {ConnectionDatagramType}

AsChannelDatagram(dgr) == dgr <: ChannelDatagramType
AsSetChannelDatagrams(Dgrs) == Dgrs <: {ChannelDatagramType}

AsPacketDatagram(dgr) == dgr <: PacketDatagramType
AsSetPacketDatagrams(Dgrs) == Dgrs <: {PacketDatagramType}
AsSeqPacketDatagrams(Dgrs) == Dgrs <: Seq(PacketDatagramType)

AsSetDatagrams(Dgrs) == Dgrs <: {DatagramType}
AsSeqDatagrams(Dgrs) == Dgrs <: Seq(DatagramType)

AsPacket(packet) == packet <: PacketType
AsSetPacket(P) == P <: {PacketType}
AsSeqPacket(P) == P <: Seq(PacketType)

AsPacketCommitment(pc) == pc <: PacketCommitmentType
AsSetPacketCommitment(PC) == PC <: {PacketCommitmentType}

AsPacketReceipt(pr) == pr <: PacketReceiptType
AsSetPacketReceipt(PR) == PR <: {PacketReceiptType}

AsPacketAcknowledgement(pa) == pa <: PacketAcknowledgementType
AsSetPacketAcknowledgement(PA) == PA <: {PacketAcknowledgementType}

AsPacketLogEntry(logEntry) == logEntry <: PacketLogEntryType
AsPacketLog(packetLog) == packetLog <: Seq(PacketLogEntryType)


(********************** Common operator definitions ***********************)
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

ClientDatagramTypes == {"CreateClient", "UpdateClient"} <: {STRING}
ConnectionDatagramTypes == {"ConnOpenInit", "ConnOpenTry", "ConnOpenAck", "ConnOpenConfirm"} <: {STRING}
ChannelDatagramTypes == {"ChanOpenInit", "ChanOpenTry", "ChanOpenAck", "ChanOpenConfirm", "ChanCloseInit", "ChanCloseConfirm"} <: {STRING}

Max(S) == CHOOSE x \in S: \A y \in S: y <= x 

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
         ] <: {ChannelEndType}
    ELSE \* set of ordered channels
         [
             state : ChannelStates,
             order : {"ORDERED"},
             nextSendSeq : 0..maxPacketSeq,
             nextRcvSeq : 0..maxPacketSeq,
             nextAckSeq : 0..maxPacketSeq, 
             channelID : ChannelIDs \union {nullChannelID},
             counterpartyChannelID : ChannelIDs \union {nullChannelID}
         ] <: {ChannelEndType}
    
    
(**************************** PacketCommitments ****************************
 A set of packet commitments.
 ***************************************************************************)
 PacketCommitments(maxHeight, maxPacketSeq) ==
    [
        channelID : ChannelIDs, 
        sequence : 1..maxPacketSeq, 
        timeoutHeight : 1..maxHeight
    ] <: {PacketCommitmentType} 
    
PacketReceipts ==
    {}
    
PacketAcknowledgements ==
    {}

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
    ] <: {ConnectionEndType} 
    
(********************************* Packets *********************************
 A set of packets.
 ***************************************************************************)
Packets(maxHeight, maxPacketSeq) ==
    [
        sequence : 1..maxPacketSeq,
        timeoutHeight : 1..maxHeight,
        srcChannelID : ChannelIDs,
        dstChannelID : ChannelIDs
    ] <: {PacketType}    

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
        packetCommitments : SUBSET(PacketCommitments(maxHeight, maxPacketSeq)),
        packetReceipts : SUBSET(PacketReceipts),
        packetsToAcknowledge : Seq(Packets(maxHeight, maxPacketSeq)),
        packetAcknowledgements : SUBSET(PacketAcknowledgements)
    ] <: {ChainStoreType}

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
    [type : {"ConnOpenTry"}, connectionID : ConnectionIDs, 
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
    <: {DatagramType}
    
NullDatagram == 
    [type |-> "null"] <: DatagramType    

NullPacketLogEntry ==
    [type |-> "null"] <: PacketLogEntryType

Histories ==
    [
        connInit : BOOLEAN,
        connTryOpen : BOOLEAN, 
        connOpen : BOOLEAN,
        chanInit : BOOLEAN,
        chanTryOpen : BOOLEAN,
        chanOpen : BOOLEAN,
        chanClosed : BOOLEAN
     ] <: {HistoryType}

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
     counterpartyChannelID |-> nullChannelID] <: ChannelEndType
     
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
     counterpartyChannelID |-> nullChannelID] <: ChannelEndType

\* Initial value of a connection end:
\*      - state is "UNINIT"
\*      - connectionID, counterpartyConnectionID are uninitialized
\*      - clientID, counterpartyClientID are uninitialized    
\*      - channelEnd is initialized based on channelOrdering      
InitConnectionEnd(channelOrdering) ==
    IF channelOrdering = "ORDERED"
    THEN [state |-> "UNINIT",
          connectionID |-> nullConnectionID,
          clientID |-> nullClientID,
          counterpartyConnectionID |-> nullConnectionID,
          counterpartyClientID |-> nullClientID,
          channelEnd |-> InitOrderedChannelEnd]
    ELSE [state |-> "UNINIT",
          connectionID |-> nullConnectionID,
          clientID |-> nullClientID,
          counterpartyConnectionID |-> nullConnectionID,
          counterpartyClientID |-> nullClientID,
          channelEnd |-> InitUnorderedChannelEnd]   
    <: ConnectionEndType       

\* Initial value of the chain store: 
\*      - height is initialized to 1
\*      - the counterparty light client is uninitialized
\*      - the connection end is initialized to InitConnectionEnd 
InitChainStore(channelOrdering) == 
    [height |-> 1,
     counterpartyClientHeights |-> AsSetInt({}), 
     connectionEnd |-> InitConnectionEnd(channelOrdering),
     packetCommitments |-> AsSetPacketCommitment({}),
     packetReceipts |-> AsSetPacketReceipt({}),
     packetsToAcknowledge |-> AsSeqPacket(<<>>),
     packetAcknowledgements |-> AsSetPacketAcknowledgement({})] <: ChainStoreType
        

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
     ]  <: HistoryType  
         
(***************************************************************************
 Client helper operators
 ***************************************************************************)

\* get the ID of chainID's counterparty chain    
GetCounterpartyChainID(chainID) ==
    IF chainID = "chainA" THEN AsID("chainB") ELSE AsID("chainA")    
 
\* get the client ID of the client for chainID 
GetClientID(chainID) ==
    IF chainID = "chainA" THEN AsID("clA") ELSE AsID("clB")
        
\* get the client ID of the client for chainID's counterparty chain           
GetCounterpartyClientID(chainID) ==
    IF chainID = "chainA" THEN AsID("clB") ELSE AsID("clA")
    
\* get the latest height of chainID
GetLatestHeight(chain) ==
    AsInt(chain.height)   
      
\* get the maximal height of the client for chainID's counterparty chain    
GetMaxCounterpartyClientHeight(chain) ==
    IF chain.counterpartyClientHeights /= AsSetInt({})
    THEN AsInt(Max(chain.counterpartyClientHeights))
    ELSE AsInt(nullHeight)

\* get the set of heights of the client for chainID's counterparty chain    
GetCounterpartyClientHeights(chain) ==
    AsSetInt(chain.counterpartyClientHeights)        

\* returns true if the counterparty client is initialized on chainID
IsCounterpartyClientOnChain(chain) ==
    AsInt(chain.counterpartyClientHeights) /= AsInt({})

\* returns true if the height h is in counterparty client heights on chainID 
IsCounterpartyClientHeightOnChain(chain, h) ==
    h \in chain.counterpartyClientHeights
     
(***************************************************************************
 Connection helper operators
 ***************************************************************************)

\* get the connection ID of the connection end at chainID
GetConnectionID(chainID) ==
    IF chainID = "chainA"
    THEN AsID("connAtoB")
    ELSE IF chainID = "chainB"
         THEN AsID("connBtoA")
         ELSE AsID(nullConnectionID)      

\* get the connection ID of the connection end at chainID's counterparty chain
GetCounterpartyConnectionID(chainID) ==
    IF chainID = "chainA"
    THEN AsID("connBtoA")
    ELSE IF chainID = "chainB"
         THEN AsID("connAtoB")
         ELSE AsID(nullConnectionID)
          
\* get the connection end at chainID
GetConnectionEnd(chain) == 
    AsConnectionEnd(chain.connectionEnd)

\* returns true if the connection end on chainID is UNINIT
IsConnectionUninit(chain) ==
    AsString(chain.connectionEnd.state) = "UNINIT"

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
    THEN AsID("chanAtoB")
    ELSE IF chainID = "chainB"
         THEN AsID("chanBtoA")
         ELSE AsID(nullChannelID)
         
\* get the channel ID of the channel end at chainID's counterparty chain
GetCounterpartyChannelID(chainID) ==
    IF chainID = "chainA"
    THEN AsID("chanBtoA")
    ELSE IF chainID = "chainB"
         THEN AsID("chanAtoB")
         ELSE AsID(nullChannelID) 
                   
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
\* Last modified Fri Sep 18 17:09:11 CEST 2020 by ilinastoilkovska
\* Created Fri Jun 05 16:56:21 CET 2020 by ilinastoilkovska