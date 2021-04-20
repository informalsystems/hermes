------------------------------- MODULE Chain -------------------------------

EXTENDS Integers, FiniteSets, Sequences, ICS04PacketHandlers, IBCPacketDelayDefinitions

CONSTANTS 
    MaxHeight, \* maximal chain height
    ChannelOrdering, \* indicate whether the channels are ordered or unordered
    MaxPacketSeq, \* maximal packet sequence number
    MaxDelay, \* maximal packet delay
    ChainID \* a chain ID

VARIABLES 
    chainStore, \* chain store, containing client heights and a channel end 
    incomingPacketDatagrams, \* sequence of incoming packet datagrams
    appPacketSeq, \* packet sequence number from the application on the chain
    packetLog, \* packet log
    packetDatagramTimestamp \* history variable that tracks when packet datagrams were processed
          
vars == <<chainStore, incomingPacketDatagrams, appPacketSeq, packetLog, packetDatagramTimestamp>>
Heights == 1..MaxHeight \* set of possible heights of the chains in the system  

(***************************************************************************
 Packet update operators
 ***************************************************************************)
\* Update the chain store and packet log with packet datagrams 
(* @type: (Str, DATAGRAM, Seq(LOGENTRY)) => 
            [chainStore: CHAINSTORE, packetLog: Seq(LOGENTRY), datagramTimestamp: <<Str, Int>> -> Int];
*)
PacketUpdate(chainID, packetDatagram, log) ==
    
    LET packet == packetDatagram.packet IN
    \* get the new updated store, packet log
    LET packetUpdate == 
        IF packetDatagram.type = "PacketRecv"
        THEN HandlePacketRecv(chainID, chainStore, packetDatagram, MaxDelay, log, packetDatagramTimestamp)
        ELSE IF packetDatagram.type = "PacketAck"
             THEN HandlePacketAck(chainID, chainStore, packetDatagram, MaxDelay, log, packetDatagramTimestamp)
             ELSE [chainStore |-> chainStore, 
                   packetLog |-> log,
                   datagramTimestamp |-> packetDatagramTimestamp]
    IN
      
    LET packetUpdateStore == packetUpdate.chainStore IN
    
    \* update height and timestamp
    LET updatedStore == 
        IF packetUpdateStore.height + 1 \in Heights 
        THEN [packetUpdateStore EXCEPT 
                !.height = packetUpdateStore.height + 1,
                !.timestamp = packetUpdateStore.timestamp + 1]
        ELSE [packetUpdateStore EXCEPT 
                !.timestamp = packetUpdateStore.timestamp + 1]
    IN
       
    [chainStore |-> updatedStore, 
     packetLog |-> packetUpdate.packetLog,
     datagramTimestamp |-> packetUpdate.datagramTimestamp]

(***************************************************************************
 Chain actions
 ***************************************************************************)       
\* Advance the height of the chain until MaxHeight is reached
AdvanceChain ==
    /\ chainStore.height + 1 \in Heights
    /\ chainStore' = [chainStore EXCEPT 
                        !.height = chainStore.height + 1,
                        !.timestamp = chainStore.timestamp + 1]
    /\ UNCHANGED <<incomingPacketDatagrams, appPacketSeq, packetLog, packetDatagramTimestamp>>

\* handle the incoming packet datagrams
HandlePacketDatagrams ==
    \* enabled if incomingPacketDatagrams is not empty
    /\ incomingPacketDatagrams /= <<>>
    /\ LET packetUpdate == PacketUpdate(ChainID, Head(incomingPacketDatagrams), packetLog) IN 
        /\ chainStore' = packetUpdate.chainStore 
        /\ packetLog' = packetUpdate.packetLog
        /\ incomingPacketDatagrams' = Tail(incomingPacketDatagrams)
        /\ packetDatagramTimestamp' = packetUpdate.datagramTimestamp
        /\ UNCHANGED appPacketSeq
        
\* Send a packet
SendPacket ==   
    \* enabled if appPacketSeq is not bigger than MaxPacketSeq 
    /\ appPacketSeq <= MaxPacketSeq
    \* Create packet  
    /\ LET packet == [
        sequence |-> appPacketSeq,
        timeoutHeight |-> MaxHeight,
        srcPortID |-> chainStore.channelEnd.portID,
        srcChannelID |-> chainStore.channelEnd.channelID,
        dstPortID |-> chainStore.channelEnd.counterpartyPortID,
        dstChannelID |-> chainStore.channelEnd.counterpartyChannelID] IN
        \* update chain store with packet committment
        /\ chainStore' = WritePacketCommitment(chainStore, packet)
        \* log sent packet
        /\ packetLog' = Append(packetLog, 
                                    [type |-> "PacketSent", 
                                     srcChainID |-> ChainID,  
                                     sequence |-> packet.sequence,
                                     timeoutHeight |-> packet.timeoutHeight]
                                  )
        \* increase application packet sequence
        /\ appPacketSeq' = appPacketSeq + 1
        /\ UNCHANGED <<incomingPacketDatagrams, packetDatagramTimestamp>>
     

       
\* Acknowledge a packet
AcknowledgePacket ==
    /\ chainStore.packetsToAcknowledge /= <<>>
    \* write acknowledgements to chain store
    /\ chainStore' = WriteAcknowledgement(chainStore, Head(chainStore.packetsToAcknowledge))
    \* log acknowledgement
    /\ packetLog' = LogAcknowledgement(ChainID, chainStore, packetLog, Head(chainStore.packetsToAcknowledge))
    /\ UNCHANGED <<incomingPacketDatagrams, appPacketSeq, packetDatagramTimestamp>> 

(***************************************************************************
 Specification
 ***************************************************************************)
\* Initial state predicate
\* Initially
\*  - the chain store is initialized to 
\*    InitChainStore(ChainID, ChannelOrdering, MaxDelay) 
\*    (defined in IBCPacketDelayDefinitions.tla)
\*  - incomingPacketDatagrams is an empty sequence
\*  - the appPacketSeq is set to 1
Init == 
    /\ chainStore = InitChainStore(ChainID, Heights, ChannelOrdering, MaxDelay)
    /\ incomingPacketDatagrams = <<>>
    /\ appPacketSeq = 1
   
\* Next state action
\* The chain either
\*  - advances its height
\*  - receives datagrams and updates its state
\*  - sends a packet
\*  - acknowledges a packet
Next ==
    \/ AdvanceChain
    \/ HandlePacketDatagrams
    \/ SendPacket
    \/ AcknowledgePacket
    \/ UNCHANGED vars   

(***************************************************************************
 Invariants
 ***************************************************************************)

\* type invariant
TypeOK ==
    /\ chainStore \in ChainStores(Heights, ChannelOrdering, MaxPacketSeq)  
    /\ incomingPacketDatagrams \in Seq(Datagrams(Heights, MaxPacketSeq))
    /\ appPacketSeq \in Int      
    /\ packetLog \in Seq(PacketLogEntries(Heights, MaxPacketSeq))

=============================================================================
\* Modification History
\* Last modified Mon Apr 19 15:44:24 CEST 2021 by ilinastoilkovska
\* Created Thu Dec 10 13:52:13 CET 2020 by ilinastoilkovska
