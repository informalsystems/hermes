----------------------------- MODULE ICS20Chain -----------------------------

EXTENDS Integers, FiniteSets, Sequences, ICS20Definitions, PacketHandlers, 
        FungibleTokenTransferHandlers
        
CONSTANTS MaxHeight, \* maximal chain height
          MaxPacketSeq, \* maximal packet sequence number
          ChainID, \* a chain ID
          EscrowAddresses, \* a set of escrow addresses
          Denomination \* denomination of tokens at ChainID 


VARIABLES chainStore, \* chain store, containing client heights, a connection end, a channel end 
          incomingPacketDatagrams, \* sequence of incoming packet datagrams
          packetLog, \* packet log
          history, \* history variable
          appPacketSeq \* packet sequence number from the application on the chain
          

vars == <<chainStore, incomingPacketDatagrams, history>>
Heights == 1..MaxHeight \* set of possible heights of the chains in the system 


TokenTransferUpdate(chainID, packetDatagram, log) ==
    LET packet == packetDatagram.packet IN
    \* get the new updated store and packet log entry
    LET newStoreAndLog == 
        IF packetDatagram.type = "PacketRecv"
        THEN HandlePacketRecv(chainID, chainStore, packetDatagram, log)
        ELSE IF packetDatagram.type = "PacketAck"
             THEN HandlePacketAck(chainID, chainStore, packetDatagram, log)
             ELSE [chainStore |-> chainStore, packetLog |-> log] IN
      
    \* update height
    LET updatedChainStore == 
        IF /\ chainStore /= newStoreAndLog.chainStore
           /\ chainStore.height + 1 \in Heights 
        THEN [newStoreAndLog.chainStore EXCEPT !.height = chainStore.height + 1]
        ELSE newStoreAndLog.chainStore
    IN
       
    [chainStore |-> updatedChainStore, 
     packetLog |-> newStoreAndLog.packetLog]       

(***************************************************************************
 Chain actions
 ***************************************************************************)       
\* Advance the height of the chain until MaxHeight is reached
AdvanceChain ==
    /\ chainStore.height + 1 \in Heights
    /\ chainStore' = [chainStore EXCEPT !.height = chainStore.height + 1]
    /\ UNCHANGED <<incomingPacketDatagrams, history>>

HandlePacketDatagrams ==
    /\ incomingPacketDatagrams /= AsSeqDatagrams(<<>>)
    /\ LET tokenTransferUpdate == TokenTransferUpdate(ChainID, Head(incomingPacketDatagrams), packetLog) IN
        /\ chainStore' = tokenTransferUpdate.store 
        /\ packetLog' = tokenTransferUpdate.log
        /\ incomingPacketDatagrams' = Tail(incomingPacketDatagrams)
     
\* Send a packet
SendPacket ==   
    \* enabled if appPacketSeq is not bigger than MaxPacketSeq 
    /\ appPacketSeq <= MaxPacketSeq
    \* Create packet data 
    /\ LET transferData == 
            CreateOutgoingPacket(<<chainStore.denomination>>, 
                                chainStore.supply,
                                ChainID,
                                GetCounterpartyChainID(ChainID),
                                chainStore.escrowAccount,
                                chainStore.vouchers) IN
    \* Create a packet: Abstract away from ports, and timestamp. 
    \* Assume timeoutHeight is MaxHeight + 1
       LET packet == AsPacket([
        sequence |-> appPacketSeq,
        timeoutHeight |-> MaxHeight + 1,
        data |-> transferData.packetData, 
        srcChannelID |-> GetChannelID(ChainID),
        dstChannelID |-> GetChannelID(GetCounterpartyChainID(ChainID))]) IN
        \* update chain store with packet committment
        /\ chainStore' = WritePacketCommitmentAndTransferData(chainStore, packet, transferData)
        \* log sent packet
        /\ packetLog' = Append(packetLog, AsPacketLogEntry(
                                               [type |-> "PacketSend", 
                                                srcChainID |-> ChainID,  
                                                sequence |-> packet.sequence ,
                                                timeoutHeight |-> packet.timeoutHeight]))
        \* increase application packet sequence
        /\ appPacketSeq' = appPacketSeq + 1
        /\ UNCHANGED <<incomingPacketDatagrams, history>>

AcknowledgePacket ==
    /\ chainStore.height + 1 \in Heights
    /\ chainStore' = [chainStore EXCEPT !.height = chainStore.height + 1]
    /\ UNCHANGED <<incomingPacketDatagrams, history>>
    /\ UNCHANGED <<packetLog, appPacketSeq>>

(***************************************************************************
 Specification
 ***************************************************************************)
\* Initial state predicate
\* Initially
\*  - the chain store is initialized to some element of the set
\*    ICS20InitChainStore(EscrowAddresses) (defined in ICS20Definitions.tla)
\*  - incomingPacketDatagrams for each chain is an empty sequence
Init == 
    /\ chainStore \in ICS20InitChainStore(ChainID, EscrowAddresses, Denomination)
    /\ incomingPacketDatagrams = <<>>
    
\* Next state action
\* The chain either
\*  - advances its height
\*  - receives datagrams and updates its state
Next ==
    \/ AdvanceChain 
    \/ HandlePacketDatagrams
    \/ SendPacket
    \/ AcknowledgePacket
    \/ UNCHANGED vars
        
Fairness ==
    /\ WF_vars(Next)        
        
(***************************************************************************
 Invariants
 ***************************************************************************)
\* Type invariant   
\* ChainStores and Datagrams are defined in ICS20Definitions.tla        
TypeOK ==    
    /\ chainStore \in ChainStores(MaxHeight, MaxPacketSeq, EscrowAddresses, Denomination)
    /\ incomingPacketDatagrams \in Seq(Datagrams(MaxHeight, MaxPacketSeq, EscrowAddresses, Denomination))
        
=============================================================================
\* Modification History
\* Last modified Thu Oct 29 20:13:49 CET 2020 by ilinastoilkovska
\* Created Mon Oct 17 13:01:03 CEST 2020 by ilinastoilkovska
