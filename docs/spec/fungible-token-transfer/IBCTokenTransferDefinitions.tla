-------------------- MODULE IBCTokenTransferDefinitions --------------------

(***************************************************************************
 This module contains definitions of operators that are shared between the 
 different modules, and which are relevant for ICS20
 ***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences

(********************* TYPE ANNOTATIONS FOR APALACHE ***********************)
\* operator for type annotations
a <: b == a

\* channel end type
ChannelEndType ==
    [
        state |-> STRING, 
        order |-> STRING, 
        channelID |-> STRING, 
        counterpartyChannelID |-> STRING,
        counterpartyPortID |-> STRING,
        version |-> STRING
    ]
    
\* ICS20 packet data type    
FungibleTokenPacketDataType ==
    [
        denomination : STRING,
        amount : Int,
        sender : STRING,
        receiver : STRING
    ] 

\* packet commitment type
PacketCommitmentType == 
    [
        channelID |-> STRING, 
        portID |-> STRING,
        sequence |-> Int, 
        data |-> FungibleTokenPacketDataType,
        timeoutHeight |-> Int
    ]
   
\* packet receipt type
PacketReceiptType ==
    [
        channelID |-> STRING, 
        portID |-> STRING,
        sequence |-> Int 
    ]    

\* packet acknowledgement type
PacketAcknowledgementType ==
    [
        channelID |-> STRING,
        portID |-> STRING, 
        sequence |-> Int,
        acknowledgement |-> BOOLEAN
    ]   

\* packet type
PacketType ==
    [
        sequence |-> Int,
        timeoutHeight |-> Int, 
        data |-> FungibleTokenPacketDataType,
        srcChainID |-> STRING,
        srcPortID |-> STRING,
        dstChainID |-> STRING,
        dstPortID |-> STRING
    ]

\* account ID type 
AccountIDType ==
    <<STRING, Seq(STRING)>>


\* chain store type 
ChainStoreType ==  
    [
        height |-> Int,
        counterpartyClientHeights |-> {Int},
        channelEnd |-> ChannelEndType,
        packetCommitments |-> {PacketCommitmentType},
        packetReceipts |-> {PacketReceiptType},
        packetAcknowledgements |-> {PacketAcknowledgementType},
        packetsToAcknowledge |-> Seq(PacketType),
        escrowAccounts |-> [AccountIDType -> Int]
    ] 

\* client datagram type
ClientDatagramType ==
    [
        type |-> STRING,
        clientID |-> STRING,
        height |-> Int   
    ]

\* datagram type (record type containing fields of all datagrams)                  
DatagramType ==
    [
        type |-> STRING,
        height |-> Int,
        clientID |-> STRING
    ]
           
\* packet log entry type    
PacketLogEntryType ==
    [
        type |-> STRING,
        srcChainID |-> STRING,
        sequence |-> Int,
        timeoutHeight |-> Int,
        acknowledgement |-> BOOLEAN,
        data |-> FungibleTokenPacketDataType
    ]
    
\* pairs of packets with acknowledgement    
PacketsToAckType ==
    <<PacketType, BOOLEAN>>    

AsID(ID) == ID <: STRING
AsInt(n) == n <: Int
AsSetID(S) == S <: {STRING}
AsSetInt(S) == S <: {Int}
AsString(s) == s <: STRING

AsChainStore(chainStore) == chainStore <: ChainStoreType

AsDatagram(dgr) == dgr <: DatagramType
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

AsSeqPacketsToAck(pa) == pa <: PacketsToAckType


(********************** Common operator definitions ***********************)
ChainIDs == {"chainA", "chainB"}
ChannelIDs == {"chanAtoB", "chanBtoA"}
PortIDs == {"portA", "portB"}
ChannelStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN", "CLOSED"}

nullHeight == 0
nullChannelID == "none"
nullPortID == "none"
nullEscrowAddress == "none"

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
        
        * for ICS20 we require that the channels are unordered
      
    - channelID -- a channel identifier
      Stores the channel identifier of this channel end.  
    
    - counterpartyChannelID -- a channel identifier
      Stores the channel identifier of the counterparty channel end. 
      
    - version -- a string
      The version is "ics20-1" for fungible token transfer
 ***************************************************************************)       
    
ChannelEnds ==
    [
        state : ChannelStates,
        order : {"UNORDERED"}, 
        channelID : ChannelIDs \union {nullChannelID},
        counterpartyChannelID : ChannelIDs \union {nullChannelID},
        counterpartyPortID : PortIDs \union {nullPortID},
        version : {"ics20-1"}
    ] 

(************************* FungibleTokenPacketData *************************
 A set of records defining ICS20 packet data.
 
 Denominations are defined as Seq(ChannelIDs \union PortIDs \union {Denomination}), 
 where Denomination is a native denomination.
 ***************************************************************************)    
FungibleTokenPacketData(maxBalance, Denominations) ==
    [
        denomination : Denominations,
        amount : 0..maxBalance,
        sender : ChainIDs,
        receiver : ChainIDs
    ]
    
(******* PacketCommitments, PacketReceipts, PacketAcknowledgements *********
 Sets of packet commitments, packet receipts, packet acknowledgements.
 ***************************************************************************)
PacketCommitments(maxHeight, maxPacketSeq, maxBalance, Denominations) ==
    [
        channelID : ChannelIDs,
        portID : PortIDs, 
        sequence : 1..maxPacketSeq,
        data : FungibleTokenPacketData(maxBalance, Denominations),
        timeoutHeight : 1..maxHeight
    ] <: {PacketCommitmentType} 
    
PacketReceipts(maxPacketSeq) ==
    [
        channelID : ChannelIDs, 
        portID : PortIDs, 
        sequence : 1..maxPacketSeq
    ] <: {PacketReceiptType}
    
PacketAcknowledgements(maxPacketSeq) ==
    [
        channelID : ChannelIDs, 
        portID : PortIDs, 
        sequence : 1..maxPacketSeq,
        acknowledgement : BOOLEAN
    ] <: {PacketAcknowledgementType}
    
(********************************* Packets *********************************
 A set of packets.
 ***************************************************************************)
Packets(maxHeight, maxPacketSeq, maxBalance, Denominations) ==
    [
        sequence : 1..maxPacketSeq,
        timeoutHeight : 1..maxHeight,
        data : FungibleTokenPacketData(maxBalance, Denominations),
        srcChannelID : ChannelIDs,
        srcPortID : PortIDs,
        dstChannelID : ChannelIDs,
        dstPortID : PortIDs
    ] <: {PacketType} 


(******************************** ChainStores ******************************
    A set of chain store records, with fields relevant for ICS20. 
    A chain store record contains the following fields:
    
    - height : an integer between nullHeight and MaxHeight. 
      Stores the current height of the chain.
    
    - channelEnd : a channel end.
    
    - packetCommitments : a set of packet commitments
      A packet commitment is added to this set when a chain sends a packet 
      to the counterparty

    - packetAcknowledgements : a set of packet acknowledgements
      A packet acknowledgement is added to this set when a chain writes an 
      acknowledgement for a packet it received from the counterparty

    - packetsToAcknowledge : a sequence of pairs <<packet, ack>>
      A pair <<packet, ack>>, where ack is a Boolean value, is added 
      to this sequence when a chain successfully receives a PacketRecv 
      datagram      
    
    A chain store is the combination of the provable and private stores.
    We do not keep track of packet receipts in the specification of ICS20, 
    these are specified in the IBC Core specification.
      
 ***************************************************************************)
ChainStores(maxHeight, maxPacketSeq, maxBalance, Denomination) ==    
    [
        height : 1..maxHeight,
        clientHeight : 1..maxHeight,
        channelEnd : ChannelEnds,
        
        packetCommitments : SUBSET(PacketCommitments(maxHeight, maxPacketSeq, maxBalance, 
                                           Seq(ChannelIDs \union PortIDs \union {Denomination}))),
        packetReceipts : SUBSET(PacketReceipts(maxPacketSeq)),
        packetAcknowledgements : SUBSET(PacketAcknowledgements(maxPacketSeq)),
        packetsToAcknowledge : Seq(Packets(maxHeight, maxPacketSeq, maxBalance, 
                                           Seq(ChannelIDs \union PortIDs \union {Denomination}))
                                   \X
                                   BOOLEAN)
    ] 
    
(******************************** Datagrams ********************************
 A set of datagrams.
 For ICS20, we need only packet datagrams
 ***************************************************************************)
Datagrams(maxHeight, maxPacketSeq, maxBalance, Denomination) ==
    [type : {"PacketRecv"}, 
     packet : Packets(maxHeight, maxPacketSeq, maxBalance, 
                      Seq(ChannelIDs \union PortIDs \union {Denomination})), 
     proofHeight : 1..maxHeight]
    \union 
    [type : {"PacketAck"}, 
     packet : Packets(maxHeight, maxPacketSeq, maxBalance, 
                      Seq(ChannelIDs \union PortIDs \union {Denomination})), 
     acknowledgement : BOOLEAN, 
     proofHeight : 1..maxHeight]
    <: {DatagramType}
          

NullDatagram == 
    [type |-> "null"] 
    <: DatagramType    
    
(***************************************************************************
 Chain helper operators
 ***************************************************************************)

\* get the ID of chainID's counterparty chain    
GetCounterpartyChainID(chainID) ==
    IF chainID = "chainA" THEN AsID("chainB") ELSE AsID("chainA")     
      
\* get the maximal height of the client for chainID's counterparty chain    
GetMaxCounterpartyClientHeight(chain) ==
    IF chain.counterpartyClientHeights /= AsSetInt({})
    THEN AsInt(Max(chain.counterpartyClientHeights))
    ELSE AsInt(nullHeight)    

\* get the channel ID of the channel end at chainID
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
     
\* get the port ID at chainID
GetPortID(chainID) ==
    IF chainID = "chainA"
    THEN AsID("portA")
    ELSE IF chainID = "chainB"
         THEN AsID("portB")
         ELSE AsID(nullPortID)      
   
\* get the port ID at chainID's counterparty chain
GetCounterpartyPortID(chainID) ==
    IF chainID = "chainA"
    THEN AsID("portB")
    ELSE IF chainID = "chainB"
         THEN AsID("portA")
         ELSE AsID(nullPortID) 

\* get the latest height of chain
GetLatestHeight(chain) ==
    AsInt(chain.height) 

(***************************************************************************
 Initial values of a channel end, chain store, accounts for ICS02
 ***************************************************************************)
\* Initial value of a channel end:
\*      - state is "OPEN" (we assume channel handshake has successfully finished)
\*      - order is "UNORDERED" (requirement of ICS20)
\*      - channelID, counterpartyChannelID 
InitUnorderedChannelEnd(ChainID) ==
    [state |-> "OPEN",
     order |-> "UNORDERED",
     channelID |-> GetChannelID(ChainID),
     counterpartyChannelID |-> GetCounterpartyChannelID(ChainID),
     counterpartyPortID |-> GetCounterpartyPortID(ChainID),
     version |-> "ics20-1"] 
  

\* A set of initial values of the chain store for ICS20: 
\*      - height is initialized to 1
\*      - counterpartyClientHeights is the set of installed client heights 
\*      - the channelEnd is initialized to InitUnorderedChannelEnd
\*      - the packet committments, receipts, acknowledgements, and packets  
\*        to acknowledge are empty
ICS20InitChainStore(ChainID, Denomination) == 
    [
        height |-> 1,
        counterpartyClientHeights |-> AsSetInt({}), 
        channelEnd |-> InitUnorderedChannelEnd(ChainID),
        
        packetCommitments |-> AsSetPacketCommitment({}),
        packetReceipts |-> AsSetPacketReceipt({}),
        packetAcknowledgements |-> AsSetPacketAcknowledgement({}),
        packetsToAcknowledge |-> AsSeqPacketsToAck(<<>>)        
    ] 

=============================================================================
\* Modification History
\* Last modified Mon Nov 23 13:06:12 CET 2020 by ilinastoilkovska
\* Created Mon Oct 17 13:01:38 CEST 2020 by ilinastoilkovska
