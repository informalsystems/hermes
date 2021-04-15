------------------------ MODULE ICS04PacketHandlers ------------------------

(***************************************************************************
 This module contains definitions of operators that are used to handle
 packet datagrams.
 ***************************************************************************)

EXTENDS Integers, FiniteSets, IBCTokenTransferDefinitions, 
        ICS20FungibleTokenTransferHandlers    

(***************************************************************************
 Packet datagram handlers
 ***************************************************************************)

\* Handle "PacketRecv" datagrams
(* @type: (Str, CHAINSTORE, DATAGRAM, Seq(LOGENTRY), ACCOUNT -> Int, ACCOUNT -> Int, Int) 
            => [store: CHAINSTORE, log: Seq(LOGENTRY), accounts: ACCOUNT -> Int, escrowAccounts: ACCOUNT -> Int];
*)
HandlePacketRecv(chainID, chain, packetDatagram, log, accounts, escrowAccounts, maxBalance) ==
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
       \* if the "PacketRecv" datagram has valid port and channel IDs 
       /\ packet.srcPortID = channelEnd.counterpartyPortID
       /\ packet.srcChannelID = channelEnd.counterpartyChannelID
       /\ packet.dstPortID = channelEnd.portID
       /\ packet.dstChannelID = channelEnd.channelID
    THEN \* call application function OnPacketRecv
         LET OnPacketRecvOutcome == 
                    OnPacketRecv(chain, accounts, escrowAccounts, packet, maxBalance) IN
         \* if OnPacketRecv is successful
         IF /\ ~OnPacketRecvOutcome.error
         \* if the packet has not been received  
            /\ [
                portID |-> packet.dstPortID, 
                channelID |-> packet.dstChannelID, 
                sequence |-> packet.sequence
               ] \notin chain.packetReceipts
         THEN \* construct log entry for packet log
              LET logEntry == [
                                type |-> "PacketRecv",
                                srcChainID |-> chainID,
                                sequence |-> packet.sequence,
                                portID |-> packet.dstPortID,
                                channelID |-> packet.dstChannelID,
                                timeoutHeight |-> packet.timeoutHeight 
                              ] IN
         
              LET updatedChainStore == [chain EXCEPT
                    \* record that the packet has been received 
                    !.packetReceipts = 
                        chain.packetReceipts 
                        \union 
                        {[
                            channelID |-> packet.dstChannelID,
                            portID |-> packet.dstPortID, 
                            sequence |-> packet.sequence
                        ]},
                    \* add packet to the set of packets for which an acknowledgement 
                    \* should be written
                    !.packetsToAcknowledge = 
                        Append(chain.packetsToAcknowledge, 
                               <<packet, OnPacketRecvOutcome.packetAck>>)
                  ] IN
              
              \* update the chain store, packet log, and bank accounts
              [store |-> updatedChainStore, 
               log |-> Append(log, logEntry), 
               accounts |-> OnPacketRecvOutcome.accounts, 
               escrowAccounts |-> OnPacketRecvOutcome.escrowAccounts] 
    
    \* otherwise, do not update the chain store, the log, the accounts               
          ELSE [store |-> chain, 
                log |-> log, 
                accounts |-> accounts, 
                escrowAccounts |-> escrowAccounts] 
    ELSE [store |-> chain, 
          log |-> log, 
          accounts |-> accounts, 
          escrowAccounts |-> escrowAccounts] 
    IN
    
    packetRecvUpdates

\* Handle "PacketAck" datagrams    
(* @type: (CHAINSTORE, DATAGRAM, Seq(LOGENTRY), ACCOUNT -> Int, ACCOUNT -> Int, Int) 
            => [store: CHAINSTORE, log: Seq(LOGENTRY), accounts: ACCOUNT -> Int, escrowAccounts: ACCOUNT -> Int];
*)
HandlePacketAck(chain, packetDatagram, log, accounts, escrowAccounts, maxBalance) ==
    \* get chainID's channel end
    LET channelEnd == chain.channelEnd IN
    \* get packet
    LET packet == packetDatagram.packet IN
    \* get acknowledgement
    LET ack == packetDatagram.acknowledgement IN
    \* get packet committment that should be in chain store
    LET packetCommitment == [
                                portID |-> packet.srcPortID, 
                                channelID |-> packet.srcChannelID, 
                                sequence |-> packet.sequence,
                                timeoutHeight |-> packet.timeoutHeight
                            ] IN
    
    \* call application function OnPacketAck
    LET OnPacketAckOutcome == 
            OnPaketAck(accounts, escrowAccounts, packet, ack, maxBalance) IN
    
    IF \* if the channel and connection ends are open for packet transmission
       /\ channelEnd.state = "OPEN"
       \* if the packet commitment exists in the chain store
       /\ packetCommitment \in chain.packetCommitments
       \* if the "PacketAck" datagram has valid port and channel IDs 
       /\ packet.srcPortID = channelEnd.portID
       /\ packet.srcChannelID = channelEnd.channelID
       /\ packet.dstPortID = channelEnd.counterpartyPortID
       /\ packet.dstChannelID = channelEnd.counterpartyChannelID
    \* remove packet commitment
    THEN LET updatedChainStore == 
                [chain EXCEPT 
                    !.packetCommitments = 
                        chain.packetCommitments \ {packetCommitment}] 
         IN

         [store |-> updatedChainStore, 
          log |-> log, 
          accounts |-> OnPacketAckOutcome.accounts, 
          escrowAccounts |-> OnPacketAckOutcome.escrowAccounts]     
          
    \* otherwise, do not update the chain store, log and accounts
    ELSE [store |-> chain, 
          log |-> log, 
          accounts |-> accounts, 
          escrowAccounts |-> escrowAccounts] 
    
    
\* write packet committments to chain store
\* @type: (CHAINSTORE, PACKET) => CHAINSTORE;
WritePacketCommitment(chain, packet) ==
    \* get channel end
    LET channelEnd == chain.channelEnd IN
    \* get latest client height
    LET latestClientHeight == GetMaxCounterpartyClientHeight(chain) IN

    IF \* channel end is neither null nor closed
       /\ channelEnd.state \notin {"UNINIT", "CLOSED"}
       \* there exists a counterparty client 
       \* (used to abstract the check if the connection end is not in UNINIT) 
       /\ latestClientHeight /= 0
       \* if the packet has valid port and channel IDs
       /\ packet.srcPortID = channelEnd.portID
       /\ packet.srcChannelID = channelEnd.channelID
       /\ packet.dstPortID = channelEnd.counterpartyPortID
       /\ packet.dstChannelID = channelEnd.counterpartyChannelID
       \* timeout height has not passed
       /\ \/ packet.timeoutHeight = 0 
          \/ latestClientHeight < packet.timeoutHeight
    THEN [chain EXCEPT 
                !.packetCommitments =  
                    chain.packetCommitments 
                    \union 
                    {[portID |-> packet.srcPortID,
                      channelID |-> packet.srcChannelID,
                      data |-> packet.data,
                      sequence |-> packet.sequence,
                      timeoutHeight |-> packet.timeoutHeight]}
         ]
         \* otherwise, do not update the chain store
         ELSE chain

\* write acknowledgements to chain store
\* @type: (CHAINSTORE, PACKETTOACK) => CHAINSTORE;
WriteAcknowledgement(chain, packetToAck) ==
    \* packetToack is a pair of a packet and its acknowledgement
    LET packet == packetToAck[1] IN
    LET ack == packetToAck[2] IN

    \* create a packet acknowledgement for this packet
    LET packetAcknowledgement == [
                                    portID |-> packet.dstPortID,
                                    channelID |-> packet.dstChannelID,
                                    sequence |-> packet.sequence,
                                    acknowledgement |-> ack
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
\* @type: (Str, CHAINSTORE, Seq(LOGENTRY), PACKETTOACK) => Seq(LOGENTRY);
LogAcknowledgement(chainID, chain, log, packetToAck) ==
    \* packetToAck is a pair of a packet and its acknowledgement
    LET packet == packetToAck[1] IN
    LET ack == packetToAck[2] IN

    \* create a packet acknowledgement for this packet
    LET packetAcknowledgement == [
                                    portID |-> packet.dstPortID,
                                    channelID |-> packet.dstChannelID,
                                    sequence |-> packet.sequence,
                                    acknowledgement |-> ack
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
                                    acknowledgement |-> ack,
                                    data |-> packet.data
                               ] IN
         Append(log, packetLogEntry)    
    \* do not add anything to the log
    ELSE log
    
\* check if a packet timed out
(* @type: (CHAINSTORE, CHAINSTORE, ACCOUNT -> Int, ACCOUNT -> Int, PACKET, Int, Int) 
            => [store: CHAINSTORE, accounts: ACCOUNT -> Int, escrowAccounts: ACCOUNT -> Int];
*)
TimeoutPacket(chain, counterpartyChain, accounts, escrowAccounts, 
              packet, proofHeight, maxBalance) ==
    \* get channel end
    LET channelEnd == chain.channelEnd IN
    \* get packet committment that should be in chain store
    LET packetCommitment == [
                                portID |-> packet.srcPortID,
                                channelID |-> packet.srcChannelID, 
                                data |-> packet.data,
                                sequence |-> packet.sequence,
                                timeoutHeight |-> packet.timeoutHeight
                            ] IN
    \* get packet receipt that should be absent in counterparty chain store
    LET packetReceipt == [
                            portID |-> packet.dstPortID,
                            channelID |-> packet.dstChannelID,
                            sequence |-> packet.sequence
                         ] IN
    
    \* call application function OnTimeoutPacket
    LET OnTimeoutPacketOutcome == 
            OnTimeoutPacket(accounts, escrowAccounts, packet, maxBalance) IN
    
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
       /\ packetReceipt \notin counterpartyChain.packetReceipts
    \* remove packet commitment
    THEN LET updatedChainStore == 
                [chain EXCEPT !.packetCommitments = 
                    chain.packetCommitments \ {packetCommitment}] IN
         [store |-> updatedChainStore,
          accounts |-> OnTimeoutPacketOutcome.accounts,
          escrowAccounts |-> OnTimeoutPacketOutcome.escrowAccounts]
          
    \* otherwise, do not update the chain store and accounts
    ELSE [store |-> chain,
          accounts |-> accounts,
          escrowAccounts |-> escrowAccounts]
        
\* check if a packet timed out on close
(* @type: (CHAINSTORE, CHAINSTORE, ACCOUNT -> Int, ACCOUNT -> Int, PACKET, Int, Int) 
            => [store: CHAINSTORE, accounts: ACCOUNT -> Int, escrowAccounts: ACCOUNT -> Int];
*)
TimeoutOnClose(chain, counterpartyChain, accounts, escrowAccounts, 
               packet, proofHeight, maxBalance) ==
    \* get channel end
    LET channelEnd == chain.channelEnd IN
    \* get counterparty channel end
    LET counterpartyChannelEnd == counterpartyChain.channelEnd IN
    
    \* get packet committment that should be in chain store
    LET packetCommitment == [
                                portID |-> packet.srcPortID,
                                channelID |-> packet.srcChannelID, 
                                data |-> packet.data,
                                sequence |-> packet.sequence,
                                timeoutHeight |-> packet.timeoutHeight
                            ] IN
     \* get packet receipt that should be absent in counterparty chain store
    LET packetReceipt == [
                            portID |-> packet.dstPortID,
                            channelID |-> packet.dstChannelID,
                            sequence |-> packet.sequence
                         ] IN
    
    \* call application function OnTimeoutPacket
    LET OnTimeoutPacketOutcome == 
            OnTimeoutPacket(accounts, escrowAccounts, packet, maxBalance) IN
    
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
       /\ counterpartyChannelEnd.order = "UNORDERED"
       /\ counterpartyChannelEnd.portID = packet.dstPortID  
       /\ counterpartyChannelEnd.channelID = packet.dstChannelID
       /\ counterpartyChannelEnd.counterpartyChannelID = packet.srcChannelID
       /\ counterpartyChannelEnd.counterpartyPortID = packet.srcPortID
       /\ counterpartyChannelEnd.version = channelEnd.version
    \* counterparty chain has not received the packet   
       /\ packetReceipt \notin counterpartyChain.packetReceipts
    \* remove packet commitment
    THEN  LET updatedChainStore == 
                [chain EXCEPT !.packetCommitments = 
                    chain.packetCommitments \ {packetCommitment}] IN
         [store |-> updatedChainStore,
          accounts |-> OnTimeoutPacketOutcome.accounts,
          escrowAccounts |-> OnTimeoutPacketOutcome.escrowAccounts]
          
    \* otherwise, do not update the chain store and accounts
    ELSE [store |-> chain,
          accounts |-> accounts,
          escrowAccounts |-> escrowAccounts]

=============================================================================
\* Modification History
\* Last modified Wed Apr 14 15:36:57 CEST 2021 by ilinastoilkovska
\* Created Thu Oct 19 18:29:58 CET 2020 by ilinastoilkovska
