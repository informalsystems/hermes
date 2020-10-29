--------------------------- MODULE PacketHandlers ---------------------------

(***************************************************************************
 This module contains definitions of operators that are used to handle
 packet datagrams
 ***************************************************************************)

EXTENDS Integers, FiniteSets, ICS20Definitions, FungibleTokenTransferHandlers    

(***************************************************************************
 Packet datagram handlers
 ***************************************************************************)

\* Handle "PacketRecv" datagrams
HandlePacketRecv(chainID, chain, packetDatagram, log) ==
    \* get chainID's channel end
    LET channelEnd == chain.connectionEnd.channelEnd IN
    \* get packet
    LET packet == packetDatagram.packet IN
    
    LET newChainStoreAndPacketLog ==
    IF \* if the channel end is open for packet transmission
       /\ channelEnd.state = "OPEN"
       \* if the packet has not passed the timeout height
       /\ \/ packet.timeoutHeight = 0 
          \/ chain.height < packet.timeoutHeight  
       \* if the "PacketRecv" datagram can be verified 
       /\ packetDatagram.srcChannelID = channelEnd.channelID
       /\ packetDatagram.dstChannelID = channelEnd.counterpartyChannelID
    THEN \* construct log entry for packet log
         LET logEntry == AsPacketLogEntry(
                            [type |-> "PacketRecv",
                             srcChainID |-> chainID,
                             sequence |-> packet.sequence,
                             channelID |-> packet.dstChannelID,
                             timeoutHeight |-> packet.timeoutHeight 
                            ]) IN
    
         \* if the packet has not been received  
         IF <<packet.dstChannelID, packet.sequence>> \notin chain.packetReceipt
         THEN LET receiptChainStore == [chain EXCEPT
                    \* record that the packet has been received 
                    !.packetReceipts = chain.packetReceipts 
                                       \union 
                                       {AsPacketReceipt(
                                        [channelID |-> packet.dstChannelID, 
                                         sequence |-> packet.sequence])},
                    \* add packet to the set of packets for which an acknowledgement should be written
                    !.packetsToAcknowledge = Append(chain.packetsToAcknowledge, packet)] IN
              
              \* update the chain store with the packet data
              LET transferChainStore == ICS20OnPacketRecv(chainID, receiptChainStore, packet) IN                                      
              
              [chainStore |-> transferChainStore, packetLog |-> Append(log, logEntry)] 
    
    \* otherwise, do not update the chain store and the log               
          ELSE [chainStore |-> chain, packetLog |-> log] 
    ELSE [chainStore |-> chain, packetLog |-> log] IN
    
    newChainStoreAndPacketLog

\* TODO     
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
    THEN \* if the channel is ordered and the packet sequence is nextAckSeq 
         LET newChainStore == 
             IF /\ channelEnd.order = "ORDERED"
                /\ packet.sequence = channelEnd.nextAckSeq
             THEN \* increase the nextAckSeq and remove packet commitment
                  [chain EXCEPT 
                        !.connectionEnd.channelEnd.nextAckSeq = 
                             chain.connectionEnd.channelEnd.nextAckSeq + 1,
                        !.packetCommitment = chain.packetCommitment \ {packetCommitment}] 
             \* otherwise, do not update the chain store  
             ELSE chain IN
              
              
         [chainStore |-> newChainStore, packetLog |-> log]     
    \* otherwise, do not update the chain store and the log
    ELSE [chainStore |-> chain, packetLog |-> log] 
    
    
\* write packet committments to chain store
WritePacketCommitmentAndTransferData(chain, packet, transferData) ==
    \* get channel end
    LET channelEnd == chain.channelEnd IN

    \* get updated escrow account from transfer data
    LET updatedEscrowAccount == transferData.escrowAccount IN
    \* get vouchers from transfer data
    LET updatedVouchers == transferData.vouchers IN
    
    IF \* channel end is neither null nor closed
       /\ channelEnd.state \notin {"UNINIT", "CLOSED"}
       \* timeout height has not passed
       /\ \/ packet.timeoutHeight = 0 
\*          \/ latestClientHeight < packet.timeoutHeight
    THEN [chain EXCEPT 
                !.packetCommitments =  
                    chain.packetCommitments \union {[channelID |-> packet.srcChannelID,
                                                     sequence |-> packet.sequence,
                                                     timeoutHeight |-> packet.timeoutHeight]},
                !.escrowAccount = updatedEscrowAccount,
                !.vouchers = updatedVouchers
         ]
         \* otherwise, do not update the chain store
         ELSE chain


\* TODO 
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
\* Last modified Thu Oct 29 20:34:48 CET 2020 by ilinastoilkovska
\* Created Thu Oct 19 18:29:58 CET 2020 by ilinastoilkovska
