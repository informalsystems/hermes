----------------------------- MODULE ICS20Chain -----------------------------

EXTENDS Integers, FiniteSets, Sequences, ICS20Definitions, PacketHandlers, 
        FungibleTokenTransferHandlers
        
CONSTANTS MaxHeight, \* maximal chain height
          MaxPacketSeq, \* maximal packet sequence number
          MaxBalance, \* maximal account balance
          ChainID, \* a chain ID
          NativeDenomination \* native denomination of tokens at ChainID 


VARIABLES chainStore, \* chain store, containing client heights, a connection end, a channel end 
          incomingPacketDatagrams, \* sequence of incoming packet datagrams
          appPacketSeq, \* packet sequence number from the application on the chain
          packetLog, \* packet log
          accounts \* a map from chainIDs and denominations to account balances
          

vars == <<chainStore, incomingPacketDatagrams, appPacketSeq, 
          packetLog, accounts>>
Heights == 1..MaxHeight \* set of possible heights of the chains in the system 

(***************************************************************************
 Token transfer operators
 ***************************************************************************)
\* Create a packet: Abstract away from timestamp. 
\* Assume timeoutHeight is MaxHeight + 1
CreatePacket(packetData) ==
    AsPacket([
        sequence |-> appPacketSeq,
        timeoutHeight |-> MaxHeight + 1,
        data |-> packetData, 
        srcChannelID |-> GetChannelID(ChainID),
        srcPortID |-> GetPortID(ChainID),
        dstChannelID |-> GetCounterpartyChannelID(ChainID),
        dstPortID |-> GetCounterpartyPortID(ChainID)
    ])

\* update packet committments and escrow accounts in the chain store
UpdatePacketCommitmentsAndEscrowAcounts(chain, packet, escrowAccounts) ==
    \* write packet committment
    LET writtenCommittmentStore == WritePacketCommitment(chain, packet) IN
    \* update escrow accounts 
    [writtenCommittmentStore EXCEPT !.escrowAccounts = escrowAccounts]
    

\* Update the chain store and packet log with ICS20 packet datagrams 
TokenTransferUpdate(chainID, packetDatagram, log) ==
    LET packet == packetDatagram.packet IN
    \* get the new updated store, packet log, and accounts
    LET tokenTransferUpdate == 
        IF packetDatagram.type = "PacketRecv"
        THEN HandlePacketRecv(chainID, chainStore, packetDatagram, log, accounts, MaxBalance)
        ELSE IF packetDatagram.type = "PacketAck"
             THEN HandlePacketAck(chainID, chainStore, packetDatagram, log, accounts, MaxBalance)
             ELSE [store |-> chainStore, log |-> log, accounts |-> accounts] IN
      
    LET tokenTransferStore == tokenTransferUpdate.store IN
    
    \* update height
    LET updatedStore == 
        IF tokenTransferStore.height + 1 \in Heights 
        THEN [tokenTransferStore EXCEPT !.height = tokenTransferStore.height + 1]
        ELSE tokenTransferStore
    IN
       
    [store |-> updatedStore, 
     log |-> tokenTransferUpdate.log, 
     accounts |-> tokenTransferUpdate.accounts]       

(***************************************************************************
 Chain actions
 ***************************************************************************)       
\* Advance the height of the chain until MaxHeight is reached
AdvanceChain ==
    /\ chainStore.height + 1 \in Heights
    /\ chainStore' = [chainStore EXCEPT !.height = chainStore.height + 1]
    /\ UNCHANGED <<incomingPacketDatagrams, appPacketSeq, packetLog, accounts>>

\* handle the incoming packet datagrams
HandlePacketDatagrams ==
    \* enabled if incomingPacketDatagrams is not empty
    /\ incomingPacketDatagrams /= AsSeqDatagrams(<<>>)
    /\ LET tokenTransferUpdate == TokenTransferUpdate(ChainID, Head(incomingPacketDatagrams), packetLog) IN 
        /\ chainStore' = tokenTransferUpdate.store 
        /\ packetLog' = tokenTransferUpdate.log
        /\ accounts' = tokenTransferUpdate.accounts
        /\ incomingPacketDatagrams' = Tail(incomingPacketDatagrams)
        /\ UNCHANGED appPacketSeq
        
\* Send a packet
SendPacket ==   
    \* enabled if appPacketSeq is not bigger than MaxPacketSeq 
    /\ appPacketSeq <= MaxPacketSeq
    \* Create packet data 
    /\ LET createOutgoingPacketOutcome == 
            CreateOutgoingPacketData(accounts, 
                                     chainStore.escrowAccounts,
                                     <<NativeDenomination>>,
                                     MaxBalance,
                                     ChainID,
                                     GetCounterpartyChainID(ChainID)) IN
        \* do nothing if there is an error       
        \/ /\ createOutgoingPacketOutcome.error
           /\ UNCHANGED vars
        \* if there is no error, send packet
        \/ /\ ~createOutgoingPacketOutcome.error
           /\ LET packet == CreatePacket(createOutgoingPacketOutcome.packetData) IN
                \* update chain store with packet committment
                /\ chainStore' = UpdatePacketCommitmentsAndEscrowAcounts(
                                chainStore, packet, createOutgoingPacketOutcome.escrowAccounts)
                \* log sent packet
                /\ packetLog' = Append(packetLog, 
                                  AsPacketLogEntry(
                                    [type |-> "PacketSent", 
                                     srcChainID |-> ChainID,  
                                     sequence |-> packet.sequence,
                                     timeoutHeight |-> packet.timeoutHeight,
                                     data |-> packet.data]
                                  ))
                \* update bank accounts 
                /\ accounts' = createOutgoingPacketOutcome.accounts
                \* increase application packet sequence
                /\ appPacketSeq' = appPacketSeq + 1
                /\ UNCHANGED incomingPacketDatagrams
     

       
\* Acknowledge a packet
AcknowledgePacket ==
    /\ chainStore.packetsToAcknowledge /= AsSeqPacketsToAck(<<>>)
    \* write acknowledgements to chain store
    /\ chainStore' = WriteAcknowledgement(chainStore, Head(chainStore.packetsToAcknowledge))
    \* log acknowledgement
    /\ packetLog' = LogAcknowledgement(ChainID, chainStore, packetLog, Head(chainStore.packetsToAcknowledge))
    /\ UNCHANGED <<incomingPacketDatagrams, accounts>>
    /\ UNCHANGED <<appPacketSeq>>

(***************************************************************************
 Specification
 ***************************************************************************)
\* Initial state predicate
\* Initially
\*  - the chain store is initialized to 
\*    ICS20InitChainStore(ChainID, <<NativeDenomination>>) 
\*    (defined in ICS20Definitions.tla)
\*  - incomingPacketDatagrams is an empty sequence
\*  - the appPacketSeq is set to 1
Init == 
    /\ chainStore = ICS20InitChainStore(ChainID, <<NativeDenomination>>)
    /\ incomingPacketDatagrams = AsSeqDatagrams(<<>>)
    /\ appPacketSeq = AsInt(1)
    
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
        
Fairness ==
    /\ WF_vars(SendPacket)        
        
=============================================================================
\* Modification History
\* Last modified Thu Nov 19 18:16:20 CET 2020 by ilinastoilkovska
\* Created Mon Oct 17 13:01:03 CEST 2020 by ilinastoilkovska
