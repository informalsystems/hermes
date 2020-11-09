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
HandlePacketRecv(chainID, chain, packetDatagram, log, accounts) ==
    \* get chainID's channel end
    LET channelEnd == chain.channelEnd IN
    \* get packet
    LET packet == packetDatagram.packet IN
    
    LET packetRecvUpdates ==
    IF \* if the channel end is open for packet transmission
       /\ channelEnd.state = "OPEN"
       \* if the packet has not passed the timeout height
       /\ \/ packet.timeoutHeight = 0 
          \/ chain.height < packet.timeoutHeight  
       \* if the "PacketRecv" datagram can be verified 
       /\ packet.srcChannelID = channelEnd.counterpartyChannelID
       /\ packet.dstChannelID = channelEnd.channelID
    THEN \* call application function ICS20OnPacketRecv
         LET ICS20OnPacketRecvOutcome == 
                    ICS20OnPacketRecv(chainID, chain, accounts, packet) IN
         \* if ICS20OnPacketRecv is successful
         IF /\ ~ICS20OnPacketRecvOutcome.error
         \* if the packet has not been received  
            /\ [channelID |-> packet.dstChannelID, sequence |-> packet.sequence] 
                \notin chain.packetReceipts
         THEN LET updatedChainStore == [chain EXCEPT
                    \* record that the packet has been received 
                    !.packetReceipts = 
                        chain.packetReceipts 
                        \union 
                        {AsPacketReceipt([channelID |-> packet.dstChannelID, 
                                          sequence |-> packet.sequence])},
                    \* add packet to the set of packets for which an acknowledgement 
                    \* should be written
                    !.packetsToAcknowledge = 
                        Append(chain.packetsToAcknowledge, 
                               <<packet, ICS20OnPacketRecvOutcome.packetAck>>),
                               
                    \* update escrow accounts 
                    !.escrowAccounts = 
                        ICS20OnPacketRecvOutcome.escrowAccounts] IN
              
              \* update the chain store, packet log, and bank accounts
              [store |-> updatedChainStore, 
               log |-> log, 
               accounts |-> ICS20OnPacketRecvOutcome.accounts] 
    
    \* otherwise, do not update the chain store, the log, the accounts               
          ELSE [store |-> chain, log |-> log, accounts |-> accounts] 
    ELSE [store |-> chain, log |-> log, accounts |-> accounts] IN
    
    packetRecvUpdates

\* Handle "PacketAck" datagrams    
HandlePacketAck(chainID, chain, packetDatagram, log, accounts) ==
    \* get chainID's channel end
    LET channelEnd == chain.channelEnd IN
    \* get packet
    LET packet == packetDatagram.packet IN
    \* get acknowledgement
    LET ack == packetDatagram.acknowledgement IN
    \* get packet committment that should be in chain store
    LET packetCommitment == AsPacketCommitment(
                             [channelID |-> packet.srcChannelID, 
                              sequence |-> packet.sequence,
                              timeoutHeight |-> packet.timeoutHeight]) IN
    
    \* call application function ICS20OnPacketAck
    LET ICS20OnPacketAckOutcome == 
            ICS20OnPaketAck(chainID, chain, accounts, packet, ack) IN
    
    IF \* if the channel and connection ends are open for packet transmission
       /\ channelEnd.state = "OPEN"
       \* if the packet commitment exists in the chain store
       /\ packetCommitment \in chain.packetCommitments
       \* if the "PacketAck" datagram can be verified 
       /\ packet.srcChannelID = channelEnd.channelID
       /\ packet.dstChannelID = channelEnd.counterpartyChannelID
    THEN LET updatedChainStore == 
                [chain EXCEPT 
                    !.packetCommitments = 
                        chain.packetCommitments \ {packetCommitment},
                    !.escrowAccounts = 
                        ICS20OnPacketAckOutcome.escrowAccounts] IN

         [store |-> updatedChainStore, 
          log |-> log, 
          accounts |-> ICS20OnPacketAckOutcome.accounts]     
    \* otherwise, do not update the chain store, log and accounts
    ELSE [store |-> chain, log |-> log, accounts |-> accounts] 
    
    
\* write packet committments to chain store
WritePacketCommitment(chain, packet) ==
    \* get channel end
    LET channelEnd == chain.channelEnd IN

    IF \* channel end is neither null nor closed
       /\ channelEnd.state \notin {"UNINIT", "CLOSED"}
       \* timeout height has not passed
       /\ \/ packet.timeoutHeight = 0 
\*          \/ latestClientHeight < packet.timeoutHeight
    THEN [chain EXCEPT 
                !.packetCommitments =  
                    chain.packetCommitments 
                    \union 
                    {[channelID |-> packet.srcChannelID,
                      sequence |-> packet.sequence,
                      timeoutHeight |-> packet.timeoutHeight]}
         ]
         \* otherwise, do not update the chain store
         ELSE chain

\* write acknowledgements to chain store
WriteAcknowledgement(chain, packetToAck) ==
    \* packetToack is a pair of a packet and its acknowledgement
    LET packet == packetToAck[1] IN
    LET ack == packetToAck[2] IN

    \* if the acknowledgement for the packet has not been written
    IF packet \notin chain.packetAcknowledgements
    THEN \* write the acknowledgement to the chain store and remove 
         \* the packet from the set of packets to acknowledge
         LET packetAcknowledgement == 
                AsPacketAcknowledgement(
                    [channelID |-> packet.dstChannelID,
                     sequence |-> packet.sequence,
                     acknowledgement |-> ack]) IN
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
LogAcknowledgement(chainID, chain, log, packetToAck) ==
    \* packetToAck is a pair of a packet and its acknowledgement
    LET packet == packetToAck[1] IN
    LET ack == packetToAck[2] IN
    
    \* if the acknowledgement for the packet has not been written
    IF packet \notin chain.packetAcknowledgements
    THEN \* append a "WriteAck" log entry to the log
         LET packetLogEntry ==
                AsPacketLogEntry(
                    [type |-> "WriteAck",
                     srcChainID |-> chainID,
                     sequence |-> packet.sequence,
                     timeoutHeight |-> packet.timeoutHeight,
                     acknowledgement |-> ack,
                     data |-> packet.data]) IN
         Append(log, packetLogEntry)    
    \* do not add anything to the log
    ELSE log
    


=============================================================================
\* Modification History
\* Last modified Fri Nov 06 20:25:45 CET 2020 by ilinastoilkovska
\* Created Thu Oct 19 18:29:58 CET 2020 by ilinastoilkovska
