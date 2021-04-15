------------------------------- MODULE Chain -------------------------------

(***************************************************************************
 This module models the behavior of a chain running the IBC Token Transfer 
 Protocol.
 
 The chain state is represented by a chain store, which is a snapshot of the
 provable and private stores, to the extent necessary for ICS20. Additionally, 
 a chain has a dedicated datagram container for packet datagrams (given by a 
 queue of datagrams that models the order in which the datagrams were submitted 
 by some relayer).
***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, IBCTokenTransferDefinitions, 
        ICS04PacketHandlers, ICS20FungibleTokenTransferHandlers
        
CONSTANTS 
    MaxHeight, \* maximal chain height
    MaxPacketSeq, \* maximal packet sequence number
    MaxBalance, \* maximal account balance
    ChainID, \* a chain ID
    NativeDenomination \* native denomination of tokens at ChainID 


VARIABLES 
    chainStore, \* chain store, containing client heights, a channel end 
    incomingPacketDatagrams, \* sequence of incoming packet datagrams
    appPacketSeq, \* packet sequence number from the application on the chain
    packetLog, \* packet log
    accounts, \* a map from chainIDs and denominations to account balances
    escrowAccounts \* a map from channelIDs and denominations to escrow account balances
          

vars == <<chainStore, incomingPacketDatagrams, appPacketSeq, 
          packetLog, accounts, escrowAccounts>>
Heights == 1..MaxHeight \* set of possible heights of the chains in the system 

(***************************************************************************
 Token transfer operators
 ***************************************************************************)
\* Create a packet: Abstract away from timestamp. 
\* Assume timeoutHeight is MaxHeight
CreatePacket(packetData) ==
    LET channelEnd == chainStore.channelEnd IN
    [
        sequence |-> appPacketSeq,
        timeoutHeight |-> MaxHeight,
        data |-> packetData, 
        srcPortID |-> channelEnd.portID,
        srcChannelID |-> channelEnd.channelID,
        dstPortID |-> channelEnd.counterpartyPortID,
        dstChannelID |-> channelEnd.counterpartyChannelID
    ]
  

\* Update the chain store and packet log with ICS20 packet datagrams 
\* @type: (Str, DATAGRAM, Seq(LOGENTRY)) => [store: CHAINSTORE, log: Seq(LOGENTRY), accounts: ACCOUNT -> Int, escrowAccounts: ACCOUNT -> Int];
TokenTransferUpdate(chainID, packetDatagram, log) ==
    LET packet == packetDatagram.packet IN
    \* get the new updated store, packet log, and accounts
    LET tokenTransferUpdate == 
        IF packetDatagram.type = "PacketRecv"
        THEN HandlePacketRecv(chainID, chainStore, packetDatagram, log, accounts, escrowAccounts, MaxBalance)
        ELSE IF packetDatagram.type = "PacketAck"
             THEN HandlePacketAck(chainStore, packetDatagram, log, accounts, escrowAccounts, MaxBalance)
             ELSE [store |-> chainStore, 
                   log |-> log, 
                   accounts |-> accounts, 
                   escrowAccounts |-> escrowAccounts]
    IN
      
    LET tokenTransferStore == tokenTransferUpdate.store IN
    
    \* update height
    LET updatedStore == 
        IF tokenTransferStore.height + 1 \in Heights 
        THEN [tokenTransferStore EXCEPT !.height = tokenTransferStore.height + 1]
        ELSE tokenTransferStore
    IN
       
    [store |-> updatedStore, 
     log |-> tokenTransferUpdate.log, 
     accounts |-> tokenTransferUpdate.accounts,
     escrowAccounts |-> tokenTransferUpdate.escrowAccounts]       

(***************************************************************************
 Chain actions
 ***************************************************************************)       
\* Advance the height of the chain until MaxHeight is reached
AdvanceChain ==
    /\ chainStore.height + 1 \in Heights
    /\ chainStore' = [chainStore EXCEPT !.height = chainStore.height + 1]
    /\ UNCHANGED <<incomingPacketDatagrams, appPacketSeq, packetLog>>
    /\ UNCHANGED <<accounts, escrowAccounts>>

\* handle the incoming packet datagrams
HandlePacketDatagrams ==
    \* enabled if incomingPacketDatagrams is not empty
    /\ incomingPacketDatagrams /= <<>>
    /\ LET tokenTransferUpdate == TokenTransferUpdate(ChainID, Head(incomingPacketDatagrams), packetLog) IN 
        /\ chainStore' = tokenTransferUpdate.store 
        /\ packetLog' = tokenTransferUpdate.log
        /\ accounts' = tokenTransferUpdate.accounts
        /\ escrowAccounts' = tokenTransferUpdate.escrowAccounts
        /\ incomingPacketDatagrams' = Tail(incomingPacketDatagrams)
        /\ UNCHANGED appPacketSeq
        
\* Send a packet
SendPacket ==   
    \* enabled if appPacketSeq is not bigger than MaxPacketSeq 
    /\ appPacketSeq <= MaxPacketSeq
    \* Create packet data 
    /\ LET createOutgoingPacketOutcome == 
            CreateOutgoingPacketData(accounts, 
                                     escrowAccounts,
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
              LET updatedChainStore == WritePacketCommitment(chainStore, packet) IN
                \* if writing the packet commitment was successful
                /\ chainStore /= updatedChainStore   
                \* update chain store with packet committment
                /\ chainStore' = updatedChainStore
                \* log sent packet
                /\ packetLog' = Append(packetLog, [
                                                    type |-> "PacketSent", 
                                                    srcChainID |-> ChainID,  
                                                    sequence |-> packet.sequence,
                                                    timeoutHeight |-> packet.timeoutHeight,
                                                    data |-> packet.data
                                                  ])
                \* update bank accounts 
                /\ accounts' = createOutgoingPacketOutcome.accounts
                \* update escrow accounts 
                /\ escrowAccounts' = createOutgoingPacketOutcome.escrowAccounts
                \* increase application packet sequence
                /\ appPacketSeq' = appPacketSeq + 1
                /\ UNCHANGED incomingPacketDatagrams
     

       
\* Acknowledge a packet
AcknowledgePacket ==
    /\ chainStore.packetsToAcknowledge /= <<>>
    \* write acknowledgements to chain store
    /\ chainStore' = WriteAcknowledgement(chainStore, Head(chainStore.packetsToAcknowledge))
    \* log acknowledgement
    /\ packetLog' = LogAcknowledgement(ChainID, chainStore, packetLog, Head(chainStore.packetsToAcknowledge))
    /\ UNCHANGED <<incomingPacketDatagrams, appPacketSeq>> 
    /\ UNCHANGED <<accounts, escrowAccounts>>

(***************************************************************************
 Specification
 ***************************************************************************)
\* Initial state predicate
\* Initially
\*  - the chain store is initialized to 
\*    ICS20InitChainStore(ChainID, <<NativeDenomination>>) 
\*    (defined in IBCTokenTransferDefinitions.tla)
\*  - incomingPacketDatagrams is an empty sequence
\*  - the appPacketSeq is set to 1
Init == 
    /\ chainStore = ICS20InitChainStore(ChainID)
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
        
Fairness ==
    /\ WF_vars(Next)
    
(***************************************************************************
 Invariants
 ***************************************************************************)
\* Type invariant   
\* ChainStores, Datagrams, PacketLogEntries are defined in IBCTokenTransferDefinitions.tla        
TypeOK ==    
    /\ chainStore \in ChainStores(Heights, MaxPacketSeq, MaxBalance, {NativeDenomination})
    /\ appPacketSeq \in 1..(MaxPacketSeq + 1)
            
        
=============================================================================
\* Modification History
\* Last modified Wed Apr 14 15:33:11 CEST 2021 by ilinastoilkovska
\* Created Mon Oct 17 13:01:03 CEST 2020 by ilinastoilkovska
