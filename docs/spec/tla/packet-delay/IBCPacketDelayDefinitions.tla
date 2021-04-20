--------------------- MODULE IBCPacketDelayDefinitions ---------------------

EXTENDS Integers, FiniteSets, Sequences

(************************ TYPE ALIASES FOR SNOWCAT *************************)
(* @typeAlias: CHAN = 
    [
        state: Str, 
        order: Str, 
        portID: Str, 
        channelID: Str, 
        counterpartyPortID: Str, 
        counterpartyChannelID: Str, 
        nextSendSeq: Int, 
        nextRcvSeq: Int, 
        nextAckSeq: Int
    ]; 
*)
(* @typeAlias: PACKET = 
    [
        sequence: Int,
        timeoutHeight: Int,
        srcPortID: Str,
        srcChannelID: Str, 
        dstPortID: Str,
        dstChannelID: Str
    ]; 
*)
(* @typeAlias: PACKETCOMM = 
    [
        portID: Str, 
        channelID: Str,
        sequence: Int,
        timeoutHeight: Int
    ]; 
*)   
(* @typeAlias: PACKETREC = 
    [
        portID: Str, 
        channelID: Str,
        sequence: Int
    ]; 
*)   
(* @typeAlias: PACKETACK = 
    [
        portID: Str, 
        channelID: Str,
        sequence: Int,
        acknowledgement: Bool
    ]; 
*)  
(* @typeAlias: CHAINSTORE = 
    [
        height: Int, 
        timestamp: Int,
        counterpartyClientHeights: Int -> Int, 
        channelEnd: CHAN, 
        packetCommitments: Set(PACKETCOMM), 
        packetsToAcknowledge: Seq(PACKET), 
        packetReceipts: Set(PACKETREC),
        packetAcknowledgements: Set(PACKETACK)
    ]; 
*) 
(* @typeAlias: DATAGRAM = 
    [
        type: Str, 
        packet: PACKET, 
        proofHeight: Int, 
        acknowledgement: Bool
    ]; 
*)
(* @typeAlias: LOGENTRY = 
    [
        type: Str, 
        srcChainID: Str, 
        sequence: Int, 
        timeoutHeight: Int, 
        acknowledgement: Bool
    ]; 
*)

(********************** Common operator definitions ***********************)
ChainIDs == {"chainA", "chainB"}
ChannelIDs == {"chanAtoB", "chanBtoA"}
PortIDs == {"portA", "portB"}
ChannelStates == {"OPEN", "CLOSED"}

nullHeight == 0
nullChannelID == "none"
nullPortID == "none"
nullEscrowAddress == "none"

Max(S) == CHOOSE x \in S: \A y \in S: y <= x

(******************************* ChannelEnds *******************************
    A set of channel end records. 
    A channel end record contains the following fields:
    
    - state -- a string 
      Stores the current state of this channel end. We assume that channel 
      handshake has successfully finished, that is, the state is either 
      "OPEN" or "CLOSED"
      
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
    
    - portID -- a port identifier
      Stores the port identifier of this channel end.  
    
    - channelID -- a channel identifier
      Stores the channel identifier of this channel end.  
    
    - counterpartyPortID -- a port identifier
      Stores the port identifier of the counterparty channel end.   
    
    - counterpartyChannelID -- a channel identifier
      Stores the channel identifier of the counterparty channel end. 
      
    Note: we omit channel versions and connection hops.
 ***************************************************************************)   
\* @type: (Str, Int) => Set(CHAN);
ChannelEnds(channelOrdering, maxPacketSeq) ==
    IF channelOrdering = "UNORDERED"
    THEN \* set of unordered channels
         [
             state : ChannelStates,
             order : {"UNORDERED"}, 
             portID : PortIDs \union {nullPortID},
             channelID : ChannelIDs \union {nullChannelID},
             counterpartyPortID : PortIDs \union {nullPortID},
             counterpartyChannelID : ChannelIDs \union {nullChannelID}
         ] 
    ELSE \* set of ordered channels
         [
             state : ChannelStates,
             order : {"ORDERED"},
             nextSendSeq : 0..maxPacketSeq,
             nextRcvSeq : 0..maxPacketSeq,
             nextAckSeq : 0..maxPacketSeq, 
             portID : PortIDs \union {nullPortID},
             channelID : ChannelIDs \union {nullChannelID},
             counterpartyPortID : PortIDs \union {nullPortID},
             counterpartyChannelID : ChannelIDs \union {nullChannelID}
         ] 


(******* PacketCommitments, PacketReceipts, PacketAcknowledgements *********)
\* Set of packet commitments
\* @type: (Set(Int), Int) => Set(PACKETCOMM);
PacketCommitments(Heights, maxPacketSeq) ==
    [
        channelID : ChannelIDs,
        portID : PortIDs, 
        sequence : 1..maxPacketSeq,
        timeoutHeight : Heights
    ] 

\* Set of packet receipts
\* @type: (Int) => Set(PACKETREC);
PacketReceipts(maxPacketSeq) ==
    [
        channelID : ChannelIDs, 
        portID : PortIDs, 
        sequence : 1..maxPacketSeq
    ]
    
\* Set of packet acknowledgements
\* @type: (Int) => Set(PACKETACK);
PacketAcknowledgements(maxPacketSeq) ==
    [
        channelID : ChannelIDs, 
        portID : PortIDs, 
        sequence : 1..maxPacketSeq,
        acknowledgement : BOOLEAN
    ] 

(********************************* Packets *********************************)
\* Set of packets
\* @type: (Set(Int), Int) => Set(PACKET);
Packets(Heights, maxPacketSeq) ==
    [
        sequence : 1..maxPacketSeq,
        timeoutHeight : Heights,
        srcPortID : PortIDs,
        srcChannelID : ChannelIDs,
        dstPortID : PortIDs,
        dstChannelID : ChannelIDs
    ]
    
(******************************** ChainStores ******************************
    A set of chain store records. 
    A chain store record contains the following fields:
    
    - height : an integer between nullHeight and MaxHeight. 
      Stores the current height of the chain.
    
    - counterpartyClientHeights : a set of integers between 1 and MaxHeight
      Stores the heights of the client for the counterparty chain.

    - connectionEnd : a connection end record 
      Stores data about the connection with the counterparty chain.

    - packetCommitments : a set of packet commitments
      A packet commitment is added to this set when a chain sends a packet 
      to the counterparty.

    - packetReceipts : a set of packet receipts
      A packet receipt is added to this set when a chain received a packet 
      from the counterparty chain.
    
    - packetsToAcknowledge : a sequence of packets
      A packet is added to this sequence when a chain receives it and is used 
      later for the receiver chain to write an acknowledgement for the packet. 
    
    - packetAcknowledgements : a set of packet acknowledgements
      A packet acknowledgement is added to this set when a chain writes an 
      acknowledgement for a packet it received from the counterparty.
        
    A chain store is the combination of the provable and private stores.
 ***************************************************************************)
\* @type: (Set(Int), Str, Int) => Set(CHAINSTORE);
ChainStores(Heights, channelOrdering, maxPacketSeq) ==    
    [
        height : Heights,
        timestamp : Int,
        counterpartyClientHeights : [Heights -> Int],
        channelEnd : ChannelEnds(channelOrdering, maxPacketSeq),
        packetCommitments : SUBSET(PacketCommitments(Heights, maxPacketSeq)),
        packetReceipts : SUBSET(PacketReceipts(maxPacketSeq)), 
        packetsToAcknowledge : Seq(Packets(Heights, maxPacketSeq)),
        packetAcknowledgements : SUBSET(PacketAcknowledgements(maxPacketSeq))
    ] 

(******************************** Datagrams ********************************)
\* Set of datagrams (we consider only packet datagrams)
\* @type: (Set(Int), Int) => Set(DATAGRAM);
Datagrams(Heights, maxPacketSeq) ==
    [
        type : {"PacketRecv"}, 
        packet : Packets(Heights, maxPacketSeq), 
        proofHeight : Heights
    ] \union [
        type : {"PacketAck"}, 
        packet : Packets(Heights, maxPacketSeq), 
        acknowledgement : BOOLEAN, 
        proofHeight : Heights
    ]
     
\* Null datagram
NullDatagram == 
    [type |-> "null"]      
    
(**************************** PacketLogEntries *****************************)
\* Set of packet log entries
\* @type: (Set(Int), Int) => Set(LOGENTRY);
PacketLogEntries(Heights, maxPacketSeq) == 
    [
        type : {"PacketSent"},
        srcChainID : ChainIDs,  
        sequence : 1..maxPacketSeq,
        timeoutHeight : Heights
    ] \union [
        type : {"PacketRecv"},
        srcChainID : ChainIDs,  
        sequence : 1..maxPacketSeq,
        portID : PortIDs,
        channelID : ChannelIDs,
        timeoutHeight : Heights
    ] \union [
        type : {"WriteAck"},
        srcChainID : ChainIDs,  
        sequence : 1..maxPacketSeq,
        portID : PortIDs,
        channelID : ChannelIDs,
        timeoutHeight : Heights,
        acknowledgement : BOOLEAN
    ]

\* Null packet log entry
NullPacketLogEntry ==
    [type |-> "null"] 
    
     
(***************************************************************************
 Chain helper operators
 ***************************************************************************)

\* get the ID of chainID's counterparty chain    
\* @type: (Str) => Str;
GetCounterpartyChainID(chainID) ==
    IF chainID = "chainA" THEN "chainB" ELSE "chainA"     
      
\* get the maximal height of the client for chainID's counterparty chain
\* @type: (CHAINSTORE) => Int;
GetMaxCounterpartyClientHeight(chain) ==
    IF DOMAIN chain.counterpartyClientHeights /= {}
    THEN Max(DOMAIN chain.counterpartyClientHeights)
    ELSE nullHeight     
     
\* get the channel ID of the channel end at chainID
\* @type: (Str) => Str;
GetChannelID(chainID) ==
    IF chainID = "chainA"
    THEN "chanAtoB"
    ELSE IF chainID = "chainB"
         THEN "chanBtoA"
         ELSE nullChannelID
         
\* get the channel ID of the channel end at chainID's counterparty chain
\* @type: (Str) => Str;
GetCounterpartyChannelID(chainID) ==
    IF chainID = "chainA"
    THEN "chanBtoA"
    ELSE IF chainID = "chainB"
         THEN "chanAtoB"
         ELSE nullChannelID 
     
\* get the port ID at chainID
\* @type: (Str) => Str;
GetPortID(chainID) ==
    IF chainID = "chainA"
    THEN "portA"
    ELSE IF chainID = "chainB"
         THEN "portB"
         ELSE nullPortID      
   
\* get the port ID at chainID's counterparty chain
\* @type: (Str) => Str;
GetCounterpartyPortID(chainID) ==
    IF chainID = "chainA"
    THEN "portB"
    ELSE IF chainID = "chainB"
         THEN "portA"
         ELSE nullPortID 
         
\* get the latest height of chain
\* @type: (CHAINSTORE) => Int;
GetLatestHeight(chain) ==
    chain.height          
         
(***************************************************************************
 Initial values of a channel end, connection end, chain store
 ***************************************************************************)
\* Initial value of an unordered channel end:
\*      - state is "OPEN" (we assume channel handshake has successfully finished)
\*      - order is "UNORDERED"
\*      - portID, channelID, counterpartyPortID, counterpartyChannelID depend on ChainID
\* @type: (Str) => CHAN;
InitUnorderedChannelEnd(ChainID) ==
    [
        state |-> "OPEN",
        order |-> "UNORDERED",
        portID |-> GetPortID(ChainID),
        channelID |-> GetChannelID(ChainID),
        counterpartyPortID |-> GetCounterpartyPortID(ChainID),
        counterpartyChannelID |-> GetCounterpartyChannelID(ChainID)
    ] 
     
\* Initial value of an ordered channel end:
\*      - state is "OPEN" (we assume channel handshake has successfully finished)
\*      - order is "ORDERED"
\*      - nextSendSeq, nextRcvSeq, nextAckSeq are set to 0
\*      - portID, channelID, counterpartyPortID, counterpartyChannelID depend on ChainID
\* @type: (Str) => CHAN;
InitOrderedChannelEnd(ChainID) ==
    [   
        state |-> "OPEN",
        order |-> "ORDERED",
        nextSendSeq |-> 0,
        nextRcvSeq |-> 0,
        nextAckSeq |-> 0,
        portID |-> GetPortID(ChainID),
        channelID |-> GetChannelID(ChainID),
        counterpartyPortID |-> GetCounterpartyPortID(ChainID),
        counterpartyChannelID |-> GetCounterpartyChannelID(ChainID)
    ]     

\* Initial value of a channel end, based on the channel ordering
\* @type: (Str, Str) => CHAN;
InitChannelEnd(ChainID, ChannelOrdering) ==
    IF ChannelOrdering = "ORDERED"
    THEN InitOrderedChannelEnd(ChainID)
    ELSE InitUnorderedChannelEnd(ChainID)

\* Initial value of the chain store: 
\*      - height is initialized to 1
\*      - timestamp is initialized to 1
\*      - there are no installed client heights
\*      - the channel end is initialized to InitChannelEnd 
\*      - the packet committments, receipts, acknowledgements, and packets  
\*        to acknowledge are empty
\* @type: (Str, Set(Int), Str, Int) => CHAINSTORE;
InitChainStore(ChainID, Heights, ChannelOrdering, MaxDelay) == 
    [
        height |-> 1,
        timestamp |-> 1,
        counterpartyClientHeights |-> [h \in Heights |-> 0], 
        channelEnd |-> InitChannelEnd(ChainID, ChannelOrdering),
        
        packetCommitments |-> {},
        packetReceipts |-> {},
        packetAcknowledgements |-> {},
        packetsToAcknowledge |-> <<>>        
    ] 
    
=============================================================================
\* Modification History
\* Last modified Mon Apr 19 15:46:15 CEST 2021 by ilinastoilkovska
\* Created Thu Dec 10 14:06:33 CET 2020 by ilinastoilkovska
    