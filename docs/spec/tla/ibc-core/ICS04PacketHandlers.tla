------------------------ MODULE ICS04PacketHandlers ------------------------

(***************************************************************************
 This module contains definitions of operators that are used to handle
 packet datagrams.
 ***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, IBCCoreDefinitions    

(***************************************************************************
 Packet datagram handlers
 ***************************************************************************)

\* Handle "PacketRecv" datagrams
\* @type: (Str, CHAINSTORE, DATAGRAM, Seq(LOGENTRY)) => [chainStore: CHAINSTORE, packetLog: Seq(LOGENTRY)];
HandlePacketRecv(chainID, chain, packetDatagram, log) ==
    \* get chainID's connection end
    LET connectionEnd == GetConnectionEnd(chain) IN
    \* get chainID's channel end
    LET channelEnd == connectionEnd.channelEnd IN
    \* get packet
    LET packet == packetDatagram.packet IN
    
    IF \* if the channel and connection ends are open for packet transmission
       /\ channelEnd.state = "OPEN"
       /\ connectionEnd.state = "OPEN" 
       \* if the packet has not passed the timeout height
       /\ \/ packet.timeoutHeight = 0 
          \/ chain.height < packet.timeoutHeight  
       \* if the "PacketRecv" datagram has valid port and channel IDs 
       /\ packet.srcPortID = channelEnd.counterpartyPortID
       /\ packet.srcChannelID = channelEnd.counterpartyChannelID
       /\ packet.dstPortID = channelEnd.portID
       /\ packet.dstChannelID = channelEnd.channelID
       \* if "PacketRecv" datagram can be verified
       /\ packetDatagram.proofHeight \in chain.counterpartyClientHeights           
    THEN \* construct log entry for packet log
         LET logEntry == [
                            type |-> "PacketRecv",
                            srcChainID |-> chainID,
                            sequence |-> packet.sequence,
                            portID |-> packet.dstPortID,
                            channelID |-> packet.dstChannelID,
                            timeoutHeight |-> packet.timeoutHeight 
                        ] IN
    
         \* if the channel is unordered and the packet has not been received  
         IF /\ channelEnd.order = "UNORDERED"
            /\ [
                portID |-> packet.dstPortID,    
                channelID |-> packet.dstChannelID, 
                sequence |-> packet.sequence
               ] \notin chain.packetReceipts
         THEN LET newChainStore == [chain EXCEPT
                    \* record that the packet has been received
                    !.packetReceipts = 
                        chain.packetReceipts 
                        \union 
                        {[
                            channelID |-> packet.dstChannelID,
                            portID |-> packet.dstPortID, 
                            sequence |-> packet.sequence
                        ]},
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
\* @type: (Str, CHAINSTORE, DATAGRAM, Seq(LOGENTRY)) => [chainStore: CHAINSTORE, packetLog: Seq(LOGENTRY)];
HandlePacketAck(chainID, chain, packetDatagram, log) ==
    \* get chainID's connection end
    LET connectionEnd == GetConnectionEnd(chain) IN
    \* get chainID's channel end
    LET channelEnd == GetChannelEnd(chain) IN
    \* get packet
    LET packet == packetDatagram.packet IN
    \* get packet committment that should be in chain store
    LET packetCommitment == [
                                portID |-> packet.srcPortID,
                                channelID |-> packet.srcChannelID, 
                                sequence |-> packet.sequence,
                                timeoutHeight |-> packet.timeoutHeight
                            ] IN
    
    IF \* if the channel and connection ends are open for packet transmission
       /\ channelEnd.state = "OPEN"
       /\ connectionEnd.state = "OPEN" 
       \* if the packet commitment exists in the chain store
       /\ packetCommitment \in chain.packetCommitments
       \* if the "PacketRecv" datagram has valid port and channel IDs 
       /\ packet.srcPortID = channelEnd.portID
       /\ packet.srcChannelID = channelEnd.channelID
       /\ packet.dstPortID = channelEnd.counterpartyPortID
       /\ packet.dstChannelID = channelEnd.counterpartyChannelID
       \* if the "PacketAck" datagram can be verified 
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
\* @type: (CHAINSTORE, PACKET) => CHAINSTORE;
WritePacketCommitment(chain, packet) ==
    \* get chainID's connection end
    LET connectionEnd == GetConnectionEnd(chain) IN
    \* get chainID's channel end
    LET channelEnd == GetChannelEnd(chain) IN
    \* get latest counterparty client height 
    LET latestClientHeight == GetMaxCounterpartyClientHeight(chain) IN
    
    IF \* channel end is neither null nor closed
       /\ channelEnd.state \notin {"UNINIT", "CLOSED"}
       \* connection end is initialized
       /\ connectionEnd.state /= "UNINIT"
       \* if the packet has valid port and channel IDs
       /\ packet.srcPortID = channelEnd.portID
       /\ packet.srcChannelID = channelEnd.channelID
       /\ packet.dstPortID = channelEnd.counterpartyPortID
       /\ packet.dstChannelID = channelEnd.counterpartyChannelID
       \* timeout height has not passed
       /\ \/ packet.timeoutHeight = 0 
          \/ latestClientHeight < packet.timeoutHeight
    THEN IF \* if the channel is ordered, check if packetSeq is nextSendSeq, 
            \* add a packet committment in the chain store, and increase nextSendSeq
            /\ channelEnd.order = "ORDERED"
            /\ packet.sequence = channelEnd.nextSendSeq
         THEN [chain EXCEPT 
                !.packetCommitments =  
                    chain.packetCommitments \union {[portID |-> packet.srcPortID,
                                                     channelID |-> packet.srcChannelID,
                                                     sequence |-> packet.sequence,
                                                     timeoutHeight |-> packet.timeoutHeight]},
                !.connectionEnd.channelEnd.nextSendSeq = channelEnd.nextSendSeq + 1
              ]
         \* otherwise, do not update the chain store
         ELSE IF \* if the channel is unordered, 
                 \* add a packet committment in the chain store
                 /\ channelEnd.order = "UNORDERED"
              THEN [chain EXCEPT 
                    !.packetCommitments =  
                        chain.packetCommitments \union {[portID |-> packet.srcPortID,
                                                         channelID |-> packet.srcChannelID,
                                                         sequence |-> packet.sequence,
                                                         timeoutHeight |-> packet.timeoutHeight]}
                   ]
              \* otherwise, do not update the chain store
              ELSE chain
    ELSE chain              

\* write acknowledgements to chain store
\* @type: (CHAINSTORE, PACKET) => CHAINSTORE;
WriteAcknowledgement(chain, packet) ==
    \* create a packet acknowledgement for this packet
    LET packetAcknowledgement == [
                                    portID |-> packet.dstPortID,
                                    channelID |-> packet.dstChannelID,
                                    sequence |-> packet.sequence,
                                    acknowledgement |-> TRUE
                                 ] IN
    
    \* if the acknowledgement for the packet has not been written
    IF packetAcknowledgement \notin chain.packetAcknowledgements
    THEN \* write the acknowledgement to the chain store and remove 
         \* the packet from the set of packets to acknowledge
         [chain EXCEPT !.packetAcknowledgements = 
                            chain.packetAcknowledgements
                            \union 
                            {packetAcknowledgement},
                       !.packetsToAcknowledge = 
                            Tail(chain.packetsToAcknowledge)]                         
    
    \* remove the packet from the sequence of packets to acknowledge
    ELSE [chain EXCEPT !.packetsToAcknowledge = 
                            Tail(chain.packetsToAcknowledge)] 

\* log acknowledgements to packet Log
\* @type: (Str, CHAINSTORE, Seq(LOGENTRY), PACKET) => Seq(LOGENTRY);
LogAcknowledgement(chainID, chain, log, packet) ==
    \* create a packet acknowledgement for this packet
    LET packetAcknowledgement == [
                                    portID |-> packet.dstPortID,
                                    channelID |-> packet.dstChannelID,
                                    sequence |-> packet.sequence,
                                    acknowledgement |-> TRUE
                                 ] IN
                                 
    \* if the acknowledgement for the packet has not been written
    IF packetAcknowledgement \notin chain.packetAcknowledgements
    THEN \* append a "WriteAck" log entry to the log
         LET packetLogEntry == [
                                type |-> "WriteAck",
                                srcChainID |-> chainID,
                                sequence |-> packet.sequence,
                                portID |-> packet.dstPortID,
                                channelID |-> packet.dstChannelID,
                                timeoutHeight |-> packet.timeoutHeight,
                                acknowledgement |-> TRUE
                               ] IN
         Append(log, packetLogEntry)    
    \* do not add anything to the log
    ELSE log
    

\* check if a packet timed out
\* @type: (CHAINSTORE, CHAINSTORE, PACKET, Int) => CHAINSTORE;
TimeoutPacket(chain, counterpartyChain, packet, proofHeight) ==
    \* get connection end 
    LET connectionEnd == GetConnectionEnd(chain) IN
    \* get channel end
    LET channelEnd == GetChannelEnd(chain) IN
    \* get counterparty channel end
    LET counterpartyChannelEnd == GetChannelEnd(counterpartyChain) IN
    
    \* get packet committment that should be in chain store
    LET packetCommitment == [
                                portID |-> packet.srcPortID,
                                channelID |-> packet.srcChannelID, 
                                sequence |-> packet.sequence,
                                timeoutHeight |-> packet.timeoutHeight
                            ] IN
    \* get packet receipt that should be absent in counterparty chain store
    LET packetReceipt == [
                            portID |-> packet.dstPortID,
                            channelID |-> packet.dstChannelID,
                            sequence |-> packet.sequence
                         ] IN 
    
    \* if channel end is open
    IF /\ channelEnd.state = "OPEN"
    \* srcChannelID and srcPortID match channel and port IDs
       /\ packet.srcPortID = channelEnd.portID
       /\ packet.srcChannelID = channelEnd.channelID
    \* dstChannelID and dstPortID match counterparty channel and port IDs
       /\ packet.dstPortID = channelEnd.counterpartyPortID
       /\ packet.dstChannelID = channelEnd.counterpartyChannelID
    \* packet has timed out
       /\ packet.timeoutHeight > 0
       /\ proofHeight >= packet.timeoutHeight
    \* chain has sent the packet 
       /\ packetCommitment \in chain.packetCommitments
    \* counterparty chain has not received the packet   
       /\ \/ /\ channelEnd.order = "ORDERED"
             /\ counterpartyChannelEnd.nextRcvSeq <= packet.sequence
          \/ /\ channelEnd.order = "UNORDERED"
             /\ packetReceipt \notin counterpartyChain.packetReceipts
    \* counterparty channel end has dstPortID and dstChannelID
       /\ counterpartyChannelEnd.portID = packet.dstPortID
       /\ counterpartyChannelEnd.channelID = packet.dstChannelID
    \* close ordered channel and remove packet commitment
    THEN LET updatedChannelEnd == [channelEnd EXCEPT
                !.state = IF channelEnd.order = "ORDERED"
                          THEN "CLOSED"
                          ELSE channelEnd.state] IN
         LET updatedConnectionEnd == [connectionEnd EXCEPT
                !.channelEnd = updatedChannelEnd] IN
         LET updatedChainStore == [chain EXCEPT 
                !.packetCommitments = 
                    chain.packetCommitments \ {packetCommitment},
                !.connectionEnd = updatedConnectionEnd] IN
                    
         updatedChainStore
          
    \* otherwise, do not update the chain store 
    ELSE chain
        
\* check if a packet timed out on close
\* @type: (CHAINSTORE, CHAINSTORE, PACKET, Int) => CHAINSTORE;
TimeoutOnClose(chain, counterpartyChain, packet, proofHeight) ==
    \* get connection end 
    LET connectionEnd == GetConnectionEnd(chain) IN
    \* get channel end
    LET channelEnd == GetChannelEnd(chain) IN
    \* get counterparty channel end
    LET counterpartyChannelEnd == GetChannelEnd(counterpartyChain) IN
    
    \* get packet committment that should be in chain store
    LET packetCommitment == [
                                portID |-> packet.srcPortID,
                                channelID |-> packet.srcChannelID, 
                                sequence |-> packet.sequence,
                                timeoutHeight |-> packet.timeoutHeight
                            ] IN
     \* get packet receipt that should be absent in counterparty chain store
    LET packetReceipt == [
                            portID |-> packet.dstPortID,
                            channelID |-> packet.dstChannelID,
                            sequence |-> packet.sequence
                         ] IN
    
 
    \* if srcChannelID and srcPortID match channel and port IDs
    IF /\ packet.srcPortID = channelEnd.portID
       /\ packet.srcChannelID = channelEnd.channelID
    \* if dstChannelID and dstPortID match counterparty channel and port IDs
       /\ packet.dstPort = channelEnd.counterpartyPortID
       /\ packet.dstChannelID = channelEnd.counterpartyChannelID
    \* chain has sent the packet  
       /\ packetCommitment \in chain.packetCommitments
    \* counterparty channel end is closed and its fields are as expected   
       /\ counterpartyChannelEnd.state = "CLOSED"
       /\ counterpartyChannelEnd.portID = packet.dstPortID  
       /\ counterpartyChannelEnd.channelID = packet.dstChannelID
       /\ counterpartyChannelEnd.counterpartyPortID = packet.srcPortID
       /\ counterpartyChannelEnd.counterpartyChannelID = packet.srcChannelID
    \* counterparty chain has not received the packet   
       /\ \/ /\ channelEnd.order = "ORDERED"
             /\ counterpartyChannelEnd.nextRcvSeq <= packet.sequence
          \/ /\ channelEnd.order = "UNORDERED"
             /\ packetReceipt \notin counterpartyChain.packetReceipts
    \* close ordered channel and remove packet commitment
    THEN LET updatedChannelEnd == [channelEnd EXCEPT
                !.state = IF channelEnd.order = "ORDERED"
                          THEN "CLOSED"
                          ELSE channelEnd.state] IN
         LET updatedConnectionEnd == [connectionEnd EXCEPT
                !.channelEnd = updatedChannelEnd] IN
         LET updatedChainStore == [chain EXCEPT 
                !.packetCommitments = 
                    chain.packetCommitments \ {packetCommitment},
                !.connectionEnd = updatedConnectionEnd] IN
                    
         updatedChainStore
         
    \* otherwise, do not update the chain store 
    ELSE chain

        
=============================================================================
\* Modification History
\* Last modified Mon Apr 12 14:22:40 CEST 2021 by ilinastoilkovska
\* Created Wed Jul 29 14:30:04 CEST 2020 by ilinastoilkovska
