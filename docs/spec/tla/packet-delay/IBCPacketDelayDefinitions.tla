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
ChannelStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN", "CLOSED"}

nullHeight == 0
nullChannelID == "none"
nullPortID == "none"
nullEscrowAddress == "none"

Max(S) == CHOOSE x \in S: \A y \in S: y <= x

(******* PacketCommitments, PacketReceipts, PacketAcknowledgements *********)
\* Set of packet commitments
PacketCommitments(maxHeight, maxPacketSeq) ==
    [
        channelID : ChannelIDs,
        portID : PortIDs, 
        sequence : 1..maxPacketSeq,
        timeoutHeight : 1..maxHeight
    ] 

\* Set of packet receipts
PacketReceipts(maxPacketSeq) ==
    [
        channelID : ChannelIDs, 
        portID : PortIDs, 
        sequence : 1..maxPacketSeq
    ]
    
\* Set of packet acknowledgements
PacketAcknowledgements(maxPacketSeq) ==
    [
        channelID : ChannelIDs, 
        portID : PortIDs, 
        sequence : 1..maxPacketSeq,
        acknowledgement : BOOLEAN
    ] 

(********************************* Packets *********************************)
\* Set of packets
Packets(maxHeight, maxPacketSeq) ==
    [
        sequence : 1..maxPacketSeq,
        timeoutHeight : 1..maxHeight,
        srcPortID : PortIDs,
        srcChannelID : ChannelIDs,
        dstPortID : PortIDs,
        dstChannelID : ChannelIDs
    ]
 

(******************************** Datagrams ********************************)
\* Set of datagrams (we consider only packet datagrams)
Datagrams(maxHeight, maxPacketSeq, maxBalance, Denomination) ==
    [type : {"PacketRecv"}, 
     packet : Packets(maxHeight, maxPacketSeq), 
     proofHeight : 1..maxHeight]
    \union 
    [type : {"PacketAck"}, 
     packet : Packets(maxHeight, maxPacketSeq), 
     acknowledgement : BOOLEAN, 
     proofHeight : 1..maxHeight]
     
\* Null datagram
NullDatagram == 
    [type |-> "null"]      
     
(***************************************************************************
 Chain helper operators
 ***************************************************************************)

\* get the ID of chainID's counterparty chain    
GetCounterpartyChainID(chainID) ==
    IF chainID = "chainA" THEN "chainB" ELSE "chainA"     
      
\* get the maximal height of the client for chainID's counterparty chain
\* @type: (CHAINSTORE) => Int;
GetMaxCounterpartyClientHeight(chain) ==
    IF DOMAIN chain.counterpartyClientHeights /= {}
    THEN Max(DOMAIN chain.counterpartyClientHeights)
    ELSE nullHeight     
     
\* get the channel ID of the channel end at chainID
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
     
\* get the port ID at chainID
GetPortID(chainID) ==
    IF chainID = "chainA"
    THEN "portA"
    ELSE IF chainID = "chainB"
         THEN "portB"
         ELSE nullPortID      
   
\* get the port ID at chainID's counterparty chain
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
InitChainStore(ChainID, ChannelOrdering, MaxDelay) == 
    [
        height |-> 1,
        timestamp |-> 1,
        counterpartyClientHeights |-> [h \in {} |-> 0], 
        channelEnd |-> InitChannelEnd(ChainID, ChannelOrdering),
        
        packetCommitments |-> {},
        packetReceipts |-> {},
        packetAcknowledgements |-> {},
        packetsToAcknowledge |-> <<>>        
    ] 

\* add ChainStore, ChannelEnds, write type invariant    
    
=============================================================================
\* Modification History
\* Last modified Wed Dec 16 17:40:36 CET 2020 by ilinastoilkovska
\* Created Thu Dec 10 14:06:33 CET 2020 by ilinastoilkovska
