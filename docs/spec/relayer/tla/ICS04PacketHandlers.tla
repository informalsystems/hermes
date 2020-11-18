--------------------------- MODULE PacketHandlers ---------------------------

(***************************************************************************
 This module contains definitions of operators that are used to handle
 packet datagrams
 ***************************************************************************)

EXTENDS Integers, FiniteSets, RelayerDefinitions    

(***************************************************************************
 Packet datagram handlers
 ***************************************************************************)

\* Handle "PacketRecv" datagrams
HandlePacketRecv(chainID, chain, packetDatagram, log) ==
    \* get chainID's connection end
    LET connectionEnd == chain.connectionEnd IN
    \* get chainID's channel end
    LET channelEnd == chain.connectionEnd.channelEnd IN
    \* get packet
    LET packet == packetDatagram.packet IN
    
    IF \* if the channel and connection ends are open for packet transmission
       /\ channelEnd.state /= "UNINIT"
       /\ channelEnd.state = "OPEN"
       /\ connectionEnd.state /= "UNINIT"
       /\ connectionEnd.state = "OPEN" 
       \* if the packet has not passed the timeout height
       /\ \/ packet.timeoutHeight = 0 
          \/ chain.height < packet.timeoutHeight  
       \* if the "PacketRecv" datagram can be verified 
       /\ packet.srcChannelID = channelEnd.counterpartyChannelID
       /\ packet.dstChannelID = channelEnd.channelID
       /\ packetDatagram.proofHeight \in chain.counterpartyClientHeights           
    THEN \* construct log entry for packet log
         LET logEntry == AsPacketLogEntry(
                            [type |-> "PacketRecv",
                             srcChainID |-> chainID,
                             sequence |-> packet.sequence,
                             channelID |-> packet.dstChannelID,
                             timeoutHeight |-> packet.timeoutHeight 
                            ]) IN
    
         \* if the channel is unordered and the packet has not been received  
         IF /\ channelEnd.order = "UNORDERED"
            /\ AsPacketReceipt([channelID |-> packet.dstChannelID, sequence |-> packet.sequence])
                    \notin chain.packetReceipts
         THEN LET newChainStore == [chain EXCEPT
                    \* record that the packet has been received 
                    !.packetReceipts = chain.packetReceipts 
                                       \union 
                                       {AsPacketReceipt(
                                        [channelID |-> packet.dstChannelID, 
                                         sequence |-> packet.sequence])},
                    \* add packet to the set of packets for which an acknowledgement should be written
                    !.packetsToAcknowledge = Append(chain.packetsToAcknowledge, packet)] IN
                                      
              [chainStore |-> newChainStore, packetLog |-> Append(log, logEntry)] 
         
         ELSE \* if the channel is ordered and the packet sequence is nextRcvSeq 
              IF /\ channelEnd.order = "ORDERED"
                 /\ packet.sequence = channelEnd.nextRcvSeq
              THEN LET newChainStore == [chain EXCEPT 
                        \* increase the nextRcvSeq
                        !.connectionEnd.channelEnd.nextRcvSeq = 
                             chain.connectionEnd.channelEnd.nextRcvSeq + 1,
                        \* add packet to the set of packets for which an acknowledgement should be written
                        !.packetsToAcknowledge = Append(chain.packetsToAcknowledge, packet)] IN             
                   
                   [chainStore |-> newChainStore, packetLog |-> Append(log, logEntry)]
 
    
    \* otherwise, do not update the chain store and the log               
              ELSE [chainStore |-> chain, packetLog |-> log]
    ELSE [chainStore |-> chain, packetLog |-> log]

    
\* Handle "PacketAck" datagrams    
HandlePacketAck(chainID, chain, packetDatagram, log) ==
    \* get chainID's connection end
    LET connectionEnd == chain.connectionEnd IN
    \* get chainID's channel end
    LET channelEnd == chain.connectionEnd.channelEnd IN
    \* get packet
    LET packet == packetDatagram.packet IN
    \* get packet committment that should be in chain store
    LET packetCommitment == AsPacketCommitment(
                             [channelID |-> packet.srcChannelID, 
                              sequence |-> packet.sequence,
                              timeoutHeight |-> packet.timeoutHeight]) IN
    
    IF \* if the channel and connection ends are open for packet transmission
       /\ channelEnd.state /= "UNINIT"
       /\ channelEnd.state = "OPEN"
       /\ connectionEnd.state /= "UNINIT"
       /\ connectionEnd.state = "OPEN" 
       \* if the packet committment exists in the chain store
       /\ packetCommitment \in chain.packetCommittments
       \* if the "PacketAck" datagram can be verified 
       /\ packet.srcChannelID = channelEnd.channelID
       /\ packet.dstChannelID = channelEnd.counterpartyChannelID
       /\ packetDatagram.proofHeight \in chain.counterpartyClientHeights 
    THEN \* if the channel is ordered and the packet sequence is nextAckSeq 
         LET newChainStore == 
             IF /\ channelEnd.order = "ORDERED"
                /\ packet.sequence = channelEnd.nextAckSeq
             THEN \* increase the nextAckSeq and remove packet commitment
                  [chain EXCEPT 
                        !.connectionEnd.channelEnd.nextAckSeq = 
                             chain.connectionEnd.channelEnd.nextAckSeq + 1,
                        !.packetCommitments = chain.packetCommitments \ {packetCommitment}] 
             \* if the channel is unordered, remove packet commitment
             ELSE IF channelEnd.order = "UNORDERED"
                  THEN [chain EXCEPT 
                            !.packetCommitments = chain.packetCommitments \ {packetCommitment}] 
                  \* otherwise, do not update the chain store
                  ELSE chain IN

         [chainStore |-> newChainStore, packetLog |-> log]     
                 
    \* otherwise, do not update the chain store and the log
    ELSE [chainStore |-> chain, packetLog |-> log] 
    
    
\* write packet committments to chain store
WritePacketCommitment(chain, packet) ==
    \* get connection end 
    LET connectionEnd == chain.connectionEnd IN
    \* get channel end
    LET channelEnd == connectionEnd.channelEnd IN
    \* get latest counterparty client height 
    LET latestClientHeight == GetMaxCounterpartyClientHeight(chain) IN
    
    IF \* channel end is neither null nor closed
       /\ channelEnd.state \notin {"UNINIT", "CLOSED"}
       \* connection end is initialized
       /\ connectionEnd.state /= "UNINIT"
       \* timeout height has not passed
       /\ \/ packet.timeoutHeight = 0 
          \/ latestClientHeight < packet.timeoutHeight
    THEN IF \* if the channel is ordered, check if packetSeq is nextSendSeq, 
            \* add a packet committment in the chain store, and increase nextSendSeq
            /\ channelEnd.order = "ORDERED"
            /\ packet.sequence = channelEnd.nextSendSeq
         THEN [chain EXCEPT 
                !.packetCommitments =  
                    chain.packetCommitments \union {[channelID |-> packet.srcChannelID,
                                                     sequence |-> packet.sequence,
                                                     timeoutHeight |-> packet.timeoutHeight]},
                !.connectionEnd.channelEnd.nextSendSeq = channelEnd.nextSendSeq + 1
              ]
         \* otherwise, do not update the chain store
         ELSE chain
    ELSE IF \* if the channel is unordered, 
            \* add a packet committment in the chain store
            /\ channelEnd.order = "UNORDERED"
         THEN [chain EXCEPT 
                !.packetCommitments =  
                    chain.packetCommitments \union {[channelID |-> packet.srcChannelID,
                                                     sequence |-> packet.sequence,
                                                     timeoutHeight |-> packet.timeoutHeight]}
              ]
         \* otherwise, do not update the chain store
         ELSE chain

\* write acknowledgements to chain store
WriteAcknowledgement(chain, packet) ==
    \* if the acknowledgement for the packet has not been written
    IF packet \notin chain.packetAcknowledgements
    THEN \* write the acknowledgement to the chain store and remove 
         \* the packet from the set of packets to acknowledge
         LET packetAcknowledgement == 
                AsPacketAcknowledgement(
                    [channelID |-> packet.dstChannelID,
                     sequence |-> packet.sequence,
                     acknowledgement |-> TRUE]) IN
         [chain EXCEPT !.packetAcknowledgements = 
                            chain.packetAcknowledgements
                            \union 
                            {packetAcknowledgement},
                       !.packetsToAcknowledge = 
                            Tail(chain.packetsToAcknowledge)]                         
    
    \* remove the packet from the set of packets to acknowledge
    ELSE [chain EXCEPT !.packetsToAcknowledge = 
                            Tail(chain.packetsToAcknowledge)] 

\* log acknowledgements to packet Log
LogAcknowledgement(chainID, chain, log, packet) ==
    \* if the acknowledgement for the packet has not been written
    IF packet \notin chain.packetAcknowledgements
    THEN \* append a "WriteAck" log entry to the log
         LET packetLogEntry ==
                AsPacketLogEntry(
                    [type |-> "WriteAck",
                     srcChainID |-> chainID,
                     sequence |-> packet.sequence,
                     timeoutHeight |-> packet.timeoutHeight,
                     acknowledgement |-> TRUE]) IN
         Append(log, packetLogEntry)    
    \* do not add anything to the log
    ELSE log
    
        
=============================================================================
\* Modification History
\* Last modified Fri Nov 06 20:43:25 CET 2020 by ilinastoilkovska
\* Created Wed Jul 29 14:30:04 CEST 2020 by ilinastoilkovska
