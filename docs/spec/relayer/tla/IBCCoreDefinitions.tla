------------------------ MODULE IBCCoreDefinitions -------------------------

(***************************************************************************
 This module contains definitions of operators that are shared between the 
 different modules.
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
        counterpartyPortID |-> STRING,
        counterpartyChannelID |-> STRING
    ]
    
\* ordered channel end type
OrderedChannelEndType == 
    [
        state |-> STRING, 
        order |-> STRING, 
        channelID |-> STRING, 
        counterpartyPortID |-> STRING,
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
        channelEnd |-> ChannelEndType,
        versions |-> {Int}
    ]

\* packet commitment type
PacketCommitmentType == 
    [
        portID |-> STRING,
        channelID |-> STRING, 
        sequence |-> Int, 
        timeoutHeight |-> Int
    ]
   
\* packet receipt type
PacketReceiptType ==
    [
        portID |-> STRING,
        channelID |-> STRING, 
        sequence |-> Int 
    ]    

\* packet acknowledgement type
PacketAcknowledgementType ==
    [
        portID |-> STRING, 
        channelID |-> STRING,
        sequence |-> Int,
        acknowledgement |-> BOOLEAN
    ]  
    
\* packet type
PacketType ==
    [
        sequence |-> Int,
        timeoutHeight |-> Int, 
        srcPortID |-> STRING,
        srcChainID |-> STRING,
        dstPortID |-> STRING,
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
        version |-> {Int},
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
        version |-> {Int},
        portID |-> STRING,
        channelID |-> STRING,
        counterpartyPortID |-> STRING,
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
AsSeqPacketReceipt(PR) == PR <: Seq(PacketReceiptType)

AsPacketAcknowledgement(pa) == pa <: PacketAcknowledgementType
AsSetPacketAcknowledgement(PA) == PA <: {PacketAcknowledgementType}

AsPacketLogEntry(logEntry) == logEntry <: PacketLogEntryType
AsPacketLog(packetLog) == packetLog <: Seq(PacketLogEntryType)


(********************** Common operator definitions ***********************)
ChainIDs == {"chainA", "chainB"} 
ClientIDs == {"clA", "clB"}
ConnectionIDs == {"connAtoB", "connBtoA"}
ChannelIDs == {"chanAtoB", "chanBtoA"}
PortIDs == {"portA", "portB"}

nullHeight == 0
nullClientID == "none"
nullConnectionID == "none"
nullChannelID == "none"
nullPortID == "none"

ConnectionStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN"}
ChannelStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN", "CLOSED"}
ChannelOrder == {"ORDERED", "UNORDERED"} 

Max(S) == CHOOSE x \in S: \A y \in S: y <= x 
Min(S) == CHOOSE x \in S: \A y \in S: y >= x 

(******************************* ChannelEnds *******************************
    A set of channel end records. 
    A channel end record contains the following fields:
    
    - state -- a string 
      Stores the current state of this channel end. It has one of the 
      following values: "UNINIT", "INIT", "TRYOPEN", "OPEN", "CLOSED".
      
    - order -- a string
      Stores whether the channel end is ordered or unordered. It has one 
      of the following values: "UNORDERED", "ORDERED".
        
        * ordered channels have three additional packet sequence fields:
           nextSendSeq -- stores the sequence number of the next packet that 
           is going to be sent,
           nextRcvSeq -- stores the sequence number of the next packet that 
           is going to be received,
           nextAckSeq -- stores the sequence number of the next packet that 
           is going to be acknowledged.
    
    - channelID -- a channel identifier
      Stores the channel identifier of this channel end.  
    
    - counterpartyPortID -- a port identifier
      Stores the counterparty port identifier of this channel end.   
    
    - counterpartyChannelID -- a channel identifier
      Stores the channel identifier of the counterparty channel end. 
      
    Note: we omit channel versions and connection hops.
 ***************************************************************************)   
ChannelEnds(channelOrdering, maxPacketSeq, maxVersion) ==
    IF channelOrdering = "UNORDERED"
    THEN \* set of unordered channels
         [
             state : ChannelStates,
             order : {"UNORDERED"}, 
             channelID : ChannelIDs \union {nullChannelID},
             counterpartyPortID : PortIDs \union {nullPortID},
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
             counterpartyPortID : PortIDs \union {nullPortID},
             counterpartyChannelID : ChannelIDs \union {nullChannelID}
         ] <: {ChannelEndType}
    
    
(******* PacketCommitments, PacketReceipts, PacketAcknowledgements *********
 Sets of packet commitments, packet receipts, packet acknowledgements.
 ***************************************************************************)
PacketCommitments(maxHeight, maxPacketSeq) ==
    [
        portID : PortIDs,
        channelID : ChannelIDs, 
        sequence : 1..maxPacketSeq, 
        timeoutHeight : 1..maxHeight
    ] <: {PacketCommitmentType} 
    
PacketReceipts(maxPacketSeq) ==
    [
        portID : PortIDs,
        channelID : ChannelIDs, 
        sequence : 1..maxPacketSeq
    ] <: {PacketReceiptType}
    
PacketAcknowledgements(maxPacketSeq) ==
    [
        portID : PortIDs,
        channelID : ChannelIDs, 
        sequence : 1..maxPacketSeq,
        acknowledgement : BOOLEAN
    ] <: {PacketAcknowledgementType}

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

    - versions -- a set of versions
      Stores the set of supported connection versions. At the end of a handshake, 
      it should be a singleton set.
      
    - channelEnd : a channel end record 
      Stores data about the channel associated with this connection end.  
 ***************************************************************************)
ConnectionEnds(channelOrdering, maxPacketSeq, maxVersion) ==
    [
        state : ConnectionStates,
        connectionID : ConnectionIDs \union {nullConnectionID},
        counterpartyConnectionID : ConnectionIDs \union {nullConnectionID},
        clientID : ClientIDs \union {nullClientID},
        counterpartyClientID : ClientIDs \union {nullClientID},
        versions : SUBSET 1..maxVersion, 
        channelEnd : ChannelEnds(channelOrdering, maxPacketSeq, maxVersion)
    ] <: {ConnectionEndType} 
    
(********************************* Packets *********************************
 A set of packets.
 ***************************************************************************)
Packets(maxHeight, maxPacketSeq) ==
    [
        sequence : 1..maxPacketSeq,
        timeoutHeight : 1..maxHeight,
        srcPortID : PortIDs,
        srcChannelID : ChannelIDs,
        dstPortID : PortIDs,
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

    - packetCommitments : a set of packet commitments
      A packet commitment is added to this set when a chain sends a packet 
      to the counterparty

    - packetReceipt : a set of packet receipts
      A packet receipt is added to this set when a chain received a packet 
      from the counterparty

    - packetAcknowledgements : a set of packet acknowledgements
      A packet acknowledgement is added to this set when a chain writes an 
      acknowledgement for a packet it received from the counterparty

    - packetsToAcknowledge : a sequence of packets 
      
 ***************************************************************************)
ChainStores(maxHeight, channelOrdering, maxPacketSeq, maxVersion) ==    
    [
        height : 1..maxHeight,
        counterpartyClientHeights : SUBSET(1..maxHeight),
        connectionEnd : ConnectionEnds(channelOrdering, maxPacketSeq, maxVersion),
        packetCommitments : SUBSET(PacketCommitments(maxHeight, maxPacketSeq)),
        packetReceipts : Seq(PacketReceipts(maxPacketSeq)), \* TODO: necessary to be a seq?
        packetAcknowledgements : SUBSET(PacketAcknowledgements(maxPacketSeq)),
        packetsToAcknowledge : Seq(Packets(maxHeight, maxPacketSeq))
    ] <: {ChainStoreType}

(******************************** Datagrams ********************************
 A set of datagrams.
 ***************************************************************************)
Datagrams(maxHeight, maxPacketSeq, maxVersion) ==
    [
        type : {"ClientCreate"}, 
        clientID : ClientIDs, 
        height : 1..maxHeight
    ] \union [
        type : {"ClientUpdate"}, 
        clientID : ClientIDs, 
        height : 1..maxHeight
    ] \union [
        type : {"ConnOpenInit"}, 
        connectionID : ConnectionIDs, 
        counterpartyConnectionID : ConnectionIDs, 
        clientID : ClientIDs, 
        counterpartyClientID : ClientIDs
    ] \union
    [
        type : {"ConnOpenTry"}, 
        desiredConnectionID : ConnectionIDs, 
        counterpartyConnectionID : ConnectionIDs, 
        clientID : ClientIDs, 
        counterpartyClientID : ClientIDs, 
        versions : SUBSET 1..maxVersion, 
        proofHeight : 1..maxHeight, 
        consensusHeight : 1..maxHeight
    ] \union [
        type : {"ConnOpenAck"}, 
        connectionID : ConnectionIDs, 
        proofHeight : 1..maxHeight, 
        consensusHeight : 1..maxHeight 
    ] \union [
        type : {"ConnOpenConfirm"}, 
        connectionID : ConnectionIDs, 
        proofHeight : 1..maxHeight
    ] \union [
        type : {"ChanOpenInit"}, 
        channelID : ChannelIDs, 
        counterpartyChannelID : ChannelIDs
    ] \union [
        type : {"ChanOpenTry"}, 
        channelID : ChannelIDs, 
        counterpartyChannelID : ChannelIDs, 
        proofHeight : 1..maxHeight
    ] \union [
        type : {"ChanOpenAck"}, 
        channelID : ChannelIDs, 
        proofHeight : 1..maxHeight
    ] \union [
        type : {"ChanOpenConfirm"}, 
        channelID : ChannelIDs, 
        proofHeight : 1..maxHeight
    ] \union [
        type : {"ChanCloseInit"}, 
        channelID : ChannelIDs
    ] \union [
        type : {"ChanCloseConfirm"}, 
        channelID : ChannelIDs, 
        proofHeight : 1..maxHeight
    ] \union [
        type : {"PacketRecv"}, 
        packet : Packets(maxHeight, maxPacketSeq), 
        proofHeight : 1..maxHeight
    ] \union [
        type : {"PacketAck"}, 
        packet : Packets(maxHeight, maxPacketSeq), 
        acknowledgement : BOOLEAN, 
        proofHeight : 1..maxHeight
    ]
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
     ] 
     <: {HistoryType}

(***************************************************************************
 Initial values of a channel end, connection end, chain
 ***************************************************************************)
\* Initial value of an unordered channel end:
\*      - state is "UNINIT"
\*      - order is "UNORDERED"
\*      - channelID, counterpartyPortID, counterpartyChannelID are uninitialized
InitUnorderedChannelEnd ==
    [
        state |-> "UNINIT",
        order |-> "UNORDERED",
        channelID |-> nullChannelID,
        counterpartyPortID |-> nullPortID,
        counterpartyChannelID |-> nullChannelID
    ] 
     
\* Initial value of an ordered channel end:
\*      - state is "UNINIT"
\*      - order is "ORDERED"
\*      - nextSendSeq, nextRcvSeq, nextAckSeq are set to 0
\*      - channelID, counterpartyPortID, counterpartyChannelID are uninitialized
InitOrderedChannelEnd ==
    [   
        state |-> "UNINIT",
        order |-> "ORDERED",
        nextSendSeq |-> 0,
        nextRcvSeq |-> 0,
        nextAckSeq |-> 0,
        channelID |-> nullChannelID,
        counterpartyPortID |-> nullPortID,
        counterpartyChannelID |-> nullChannelID
    ] 

\* Initial value of a connection end:
\*      - state is "UNINIT"
\*      - connectionID, counterpartyConnectionID are uninitialized
\*      - clientID, counterpartyClientID are uninitialized  
\*      - versions is an arbitrary subset of the set {1, .., maxVersion}   
\*      - channelEnd is initialized based on channelOrdering      
InitConnectionEnds(maxVersion, channelOrdering) ==
    IF channelOrdering = "ORDERED"
    THEN [
            state : {"UNINIT"},
            connectionID : {nullConnectionID},
            clientID : {nullClientID},
            counterpartyConnectionID : {nullConnectionID},
            counterpartyClientID : {nullClientID},
            versions : (SUBSET 1..maxVersion) \ {{}},
            channelEnd : {InitOrderedChannelEnd}
         ]
    ELSE [
            state : {"UNINIT"},
            connectionID : {nullConnectionID},
            clientID : {nullClientID},
            counterpartyConnectionID : {nullConnectionID},
            counterpartyClientID : {nullClientID},
            versions : (SUBSET 1..maxVersion) \ {{}},
            channelEnd : {InitUnorderedChannelEnd}
         ]   

\* Initial value of the chain store: 
\*      - height is initialized to 1
\*      - the counterparty light client is uninitialized
\*      - the connection end is initialized to InitConnectionEnd 
InitChainStore(maxVersion, channelOrdering) == 
    [
        height : {1},
        counterpartyClientHeights : {AsSetInt({})}, 
        connectionEnd : InitConnectionEnds(maxVersion, channelOrdering),
        
        packetCommitments : {AsSetPacketCommitment({})},
        packetReceipts : {AsSeqPacketReceipt(<<>>)},
        packetAcknowledgements : {AsSetPacketAcknowledgement({})},
        packetsToAcknowledge : {AsSeqPacket(<<>>)}
        
    ] 
    <: {ChainStoreType}
        

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
    
\* pick the minimal version from a set of versions
PickVersion(versions) == 
    IF versions /= AsSetInt({})
    THEN LET minVersion == Min(versions) IN
         {minVersion}
    ELSE AsSetInt({})
    

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
\* Last modified Thu Nov 26 17:44:34 CET 2020 by ilinastoilkovska
\* Created Fri Jun 05 16:56:21 CET 2020 by ilinastoilkovska