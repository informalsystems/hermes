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
       /\ packetDatagram.srcChannelID = GetCounterpartyChannelID(chainID)
       /\ packetDatagram.dstChannelID = GetChannelID(chainID)
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
            /\ <<packet.dstChannelID, packet.sequence>> \notin chain.packetReceipt
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
                              timeoutHeihgt |-> packet.timeoutHeight]) IN
    
    IF \* if the channel and connection ends are open for packet transmission
       /\ channelEnd.state /= "UNINIT"
       /\ channelEnd.state = "OPEN"
       /\ connectionEnd.state /= "UNINIT"
       /\ connectionEnd.state = "OPEN" 
       \* if the packet committment exists in the chain store
       /\ packetCommitment \in chain.packetCommittments
       \* if the "PacketAck" datagram can be verified 
       /\ packetDatagram.srcChannelID = GetChannelID(chainID)
       /\ packetDatagram.dstChannelID = GetCounterpartyChannelID(chainID)
       /\ packetDatagram.proofHeight \in chain.counterpartyClientHeights 
    THEN \* if the channel is ordered and the packet sequence is nextAckSeq 
         LET newChainStore == 
             IF /\ channelEnd.order = "ORDERED"
                /\ packet.sequence = channelEnd.nextAckSeq
             THEN \* increase the nextAckSeq and remove packet commitment
                  [chain EXCEPT 
                        !.connectionEnd.channelEnd.nextAckSeq = 
                             chain.connectionEnd.channelEnd.nextAckSeq + 1,
                        !.packetCommitment = chain.packetCommitment \ {packetCommitment}] 
               
             ELSE \* remove packet commitment  
                  [chain EXCEPT 
                        !.packetCommitment = chain.packetCommitment \ {packetCommitment}] IN
              
              
         [chainStore |-> newChainStore, packetLog |-> log]     
    \* otherwise, do not update the chain store and the log
    ELSE [chainStore |-> chain, packetLog |-> log] 
    
        
=============================================================================
\* Modification History
\* Last modified Tue Sep 22 14:21:10 CEST 2020 by ilinastoilkovska
\* Created Wed Jul 29 14:30:04 CEST 2020 by ilinastoilkovska
