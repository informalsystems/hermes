--------------------- MODULE IBCPacketDelayDefinitions ---------------------

EXTENDS Integers, FiniteSets, Sequences

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

(******* PacketCommitments, PacketReceipts, PacketAcknowledgements *********
 Sets of packet commitments, packet receipts, packet acknowledgements.
 ***************************************************************************)
PacketCommitments(maxHeight, maxPacketSeq) ==
    [
        channelID : ChannelIDs,
        portID : PortIDs, 
        sequence : 1..maxPacketSeq,
        timeoutHeight : 1..maxHeight
    ] 
    
PacketReceipts(maxPacketSeq) ==
    [
        channelID : ChannelIDs, 
        portID : PortIDs, 
        sequence : 1..maxPacketSeq
    ]
    
PacketAcknowledgements(maxPacketSeq) ==
    [
        channelID : ChannelIDs, 
        portID : PortIDs, 
        sequence : 1..maxPacketSeq,
        acknowledgement : BOOLEAN
    ] 

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
    ]
 

(******************************** Datagrams ********************************
 A set of datagrams.
 We consider client and packet datagrams
 ***************************************************************************)
Datagrams(maxHeight, maxPacketSeq, maxBalance, Denomination) ==
    [type : {"PacketRecv"}, 
     packet : Packets(maxHeight, maxPacketSeq), 
     proofHeight : 1..maxHeight]
    \union 
    [type : {"PacketAck"}, 
     packet : Packets(maxHeight, maxPacketSeq), 
     acknowledgement : BOOLEAN, 
     proofHeight : 1..maxHeight]
     
NullDatagram == 
    [type |-> "null"]      
     
(***************************************************************************
 Chain helper operators
 ***************************************************************************)

\* get the ID of chainID's counterparty chain    
GetCounterpartyChainID(chainID) ==
    IF chainID = "chainA" THEN "chainB" ELSE "chainA"     
      
\* get the maximal height of the client for chainID's counterparty chain
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

InitChannelEnd(ChainID, ChannelOrdering) ==
    IF ChannelOrdering = "ORDERED"
    THEN InitOrderedChannelEnd(ChainID)
    ELSE InitUnorderedChannelEnd(ChainID)

\* Initial value of the chain store: 
\*      - height is initialized to 1
\*      - timestamp is initialized to 0
\*      - the counterparty client is created at timestamp 1
\*      - the channel end is initialized to InitConnectionEnd 
InitChainStore(ChainID, ChannelOrdering, MaxDelay) == 
    [
        height |-> 1,
        timestamp |-> 1,
        counterpartyClientHeights |-> [h \in {1} |-> 1], 
        channelEnd |-> InitChannelEnd(ChainID, ChannelOrdering),
        
        packetCommitments |-> {},
        packetReceipts |-> {},
        packetAcknowledgements |-> {},
        packetsToAcknowledge |-> <<>>        
    ] 
    
=============================================================================
\* Modification History
\* Last modified Tue Dec 15 15:53:32 CET 2020 by ilinastoilkovska
\* Created Thu Dec 10 14:06:33 CET 2020 by ilinastoilkovska
