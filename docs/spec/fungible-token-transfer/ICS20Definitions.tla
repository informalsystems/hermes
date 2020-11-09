-------------------------- MODULE ICS20Definitions --------------------------

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
        counterpartyChannelID |-> STRING
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

\* ICS20 packet data type    
FungibleTokenPacketDataType ==
    [
        denomination : STRING,
        amount : Int,
        sender : STRING,
        receiver : STRING
    ]    

\* packet type
PacketType ==
    [
        sequence |-> Int,
        timeoutHeight |-> Int, 
        data |-> FungibleTokenPacketDataType,
        srcChainID |-> STRING,
        dstChainID |-> STRING
    ]


\* chain store type 
ChainStoreType ==  
    [
        height |-> Int,
        channelEnd |-> ChannelEndType,
        packetCommitments |-> {PacketCommitmentType},
        packetsToAcknowledge |-> Seq(PacketType),
        packetReceipts |-> {PacketReceiptType},
        packetAcknowledgements |-> {PacketAcknowledgementType}
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
ChannelStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN", "CLOSED"}

nullHeight == 0
nullChannelID == "none"
nullEscrowAddress == "none"

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
 ***************************************************************************)       
    
ChannelEnds ==
    [
        state : ChannelStates,
        order : {"UNORDERED"}, 
        channelID : ChannelIDs \union {nullChannelID},
        counterpartyChannelID : ChannelIDs \union {nullChannelID}
    ] 
    
(******* PacketCommitments, PacketReceipts, PacketAcknowledgements *********
 Sets of packet commitments, packet receipts, packet acknowledgements.
 ***************************************************************************)
PacketCommitments(maxHeight, maxPacketSeq) ==
    [
        channelID : ChannelIDs, 
        sequence : 1..maxPacketSeq, 
        timeoutHeight : 1..maxHeight
    ] <: {PacketCommitmentType} 
    
PacketReceipts(maxPacketSeq) ==
    [
        channelID : ChannelIDs, 
        sequence : 1..maxPacketSeq
    ] <: {PacketReceiptType}
    
PacketAcknowledgements(maxPacketSeq) ==
    [
        channelID : ChannelIDs, 
        sequence : 1..maxPacketSeq,
        acknowledgement : BOOLEAN
    ] <: {PacketAcknowledgementType}
    
(************************* FungibleTokenPacketData *************************
 A set of records defining ICS20 packet data.
 
 Denominations are defined as Seq(ChannelIDs \cup {Denomination}), 
 where Denomination is a native denomination.
 ***************************************************************************)    
FungibleTokenPacketData(maxBalance, Denominations) ==
    [
        denomination : Denominations,
        amount : 0..maxBalance,
        sender : ChainIDs,
        receiver : ChainIDs
    ]

(********************************* Packets *********************************
 A set of packets.
 ***************************************************************************)
Packets(maxHeight, maxPacketSeq, maxBalance, Denominations) ==
    [
        sequence : 1..maxPacketSeq,
        timeoutHeight : 1..maxHeight,
        data : FungibleTokenPacketData(maxBalance, Denominations),
        srcChannelID : ChannelIDs,
        dstChannelID : ChannelIDs
    ] <: {PacketType} 


(******************************** ChainStores ******************************
    A set of chain store records, with fields relevant for ICS20. 
    A chain store record contains the following fields:
    
    - height : an integer between nullHeight and MaxHeight. 
      Stores the current height of the chain.
    
    - channelEnd : a channel end.
    
      
 ***************************************************************************)
ChainStores(maxHeight, maxPacketSeq, maxBalance, Denomination) ==    
    [
        height : 1..maxHeight,
        channelEnd : ChannelEnds,
        
        packetCommitments : SUBSET(PacketCommitments(maxHeight, maxPacketSeq)),
        packetReceipts : SUBSET(PacketReceipts(maxPacketSeq)),
        packetsToAcknowledge : Seq(Packets(maxHeight, maxPacketSeq, maxBalance, 
                                           Seq(ChannelIDs \cup {Denomination}))
                                   \X
                                   BOOLEAN),
        packetAcknowledgements : SUBSET(PacketAcknowledgements(maxPacketSeq))
    ] 
    
(******************************** Datagrams ********************************
 A set of datagrams.
 ***************************************************************************)
Datagrams(maxHeight, maxPacketSeq, maxBalance, Denomination) ==
    [type : {"PacketRecv"}, 
     packet : Packets(maxHeight, maxPacketSeq, maxBalance, Seq(ChannelIDs \cup {Denomination})), 
     proofHeight : 1..maxHeight]
    \union 
    [type : {"PacketAck"}, 
     packet : Packets(maxHeight, maxPacketSeq, maxBalance, Seq(ChannelIDs \cup {Denomination})), 
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

\* get the latest height of chain
GetLatestHeight(chain) ==
    AsInt(chain.height) 

\* get the escrow accounts of chain         
GetEscrowAccounts(chain) ==
    chain.escrowAccounts    

\* get the account ballance of an escrow account on chain given a denomination         
GetEscrowAccountBalance(chain, denomination) ==
    chain.escrowAccounts[denomination]    
                       

(***************************************************************************
 Initial values of a channel end, chain store, accounts for ICS02
 ***************************************************************************)
\* Initial value of a channel end:
\*      - state is "OPEN" (we assume channel handshake has successfully finished)
\*      - order is "UNORDERED" (requirement of ICS20)
\*      - channelID, counterpartyChannelID are uninitialized
InitUnorderedChannelEnd(ChainID) ==
    [state |-> "OPEN",
     order |-> "UNORDERED",
     channelID |-> GetChannelID(ChainID),
     counterpartyChannelID |-> GetCounterpartyChannelID(ChainID)] 

\* A set of initial values of the chain store for ICS20: 
\*      - height is initialized to 1
\*      - the channelEnd is initialized to InitUnorderedChannelEnd
\*      - the channelEscrowAddress is initialized to some address in EscrowAddresses
\*      - the packet committments, receipts, acknowledgements, and packets to acknowledge 
\*        are empty
\*      - the bank accouts and escrow accounts are functions that initially 
\*        map the native denomination to maxBalance and 0, respectively 
ICS20InitChainStore(ChainID, Denomination) == 
    [
        height |-> 1,
        channelEnd |-> InitUnorderedChannelEnd(ChainID),
        
        packetCommitments |-> AsSetPacketCommitment({}),
        packetReceipts |-> AsSetPacketReceipt({}),
        packetsToAcknowledge |-> AsSeqPacketsToAck(<<>>),
        packetAcknowledgements |-> AsSetPacketAcknowledgement({}),
        
        escrowAccounts |-> [<<chanID, denom>> \in {<<GetChannelID(ChainID), Denomination>>} |-> 0]
    ] 

=============================================================================
\* Modification History
\* Last modified Fri Nov 06 15:57:22 CET 2020 by ilinastoilkovska
\* Created Mon Oct 17 13:01:38 CEST 2020 by ilinastoilkovska
