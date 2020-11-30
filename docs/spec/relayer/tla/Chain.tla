---------------------------- MODULE Chain ----------------------------

EXTENDS Integers, FiniteSets, IBCCoreDefinitions, 
        ICS02ClientHandlers, ICS03ConnectionHandlers, 
        ICS04ChannelHandlers, ICS04PacketHandlers
        
CONSTANTS MaxHeight, \* maximal chain height
          ChainID, \* chain identifier
          ChannelOrdering, \* indicate whether the channels are ordered or unordered  
          MaxVersion, \* maximal connection / channel version (we assume versions are integers)
          MaxPacketSeq \* maximal packet sequence number

VARIABLES chainStore, \* chain store, containing client heights, a connection end, a channel end 
          incomingDatagrams, \* set of incoming datagrams
          incomingPacketDatagrams, \* sequence of incoming packet datagrams
          history, \* history variable
          packetLog, \* packet log
          appPacketSeq \* packet sequence number from the application on the chain

vars == <<chainStore, incomingDatagrams, incomingPacketDatagrams, 
           history, packetLog, appPacketSeq>>
Heights == 1..MaxHeight \* set of possible heights of the chains in the system          

(***************************************************************************
 Client update operators
 ***************************************************************************)
\* Update the clients on chain with chainID, 
\* using the client datagrams generated by the relayer      
\* (Handler operators defined in ICS02ClientHandlers.tla)
LightClientUpdate(chainID, store, datagrams) == 
    \* create clients
    LET clientCreatedStore == HandleCreateClient(chainID, store, datagrams) IN
    \* update clients
    LET clientUpdatedStore == HandleClientUpdate(chainID, clientCreatedStore, datagrams) IN

    clientUpdatedStore

(***************************************************************************
 Connection update operators
 ***************************************************************************)
\* Update the connections on chain with chainID, 
\* using the connection datagrams generated by the relayer
\* (Handler operators defined in ICS03ConnectionHandlers.tla)
ConnectionUpdate(chainID, store, datagrams) ==
    \* update the chain store with "ConnOpenInit" datagrams
    LET connOpenInitStore == HandleConnOpenInit(chainID, store, datagrams) IN
    
    \* update the chain store with "ConnOpenTry" datagrams
    LET connOpenTryStore == HandleConnOpenTry(chainID, connOpenInitStore, datagrams) IN
    
    \* update the chain store with "ConnOpenAck" datagrams
    LET connOpenAckStore == HandleConnOpenAck(chainID, connOpenTryStore, datagrams) IN
    
    \* update the chain store with "ConnOpenConfirm" datagrams
    LET connOpenConfirmStore == HandleConnOpenConfirm(chainID, connOpenAckStore, datagrams) IN
    
    \* output the updated chain store 
    connOpenConfirmStore
    
(***************************************************************************
 Channel update operators
 ***************************************************************************)
\* Update the channel on chain with chainID, 
\* using the channel datagrams generated by the relayer
\* (Handler operators defined in ICS04ChannelHandlers.tla)
ChannelUpdate(chainID, store, datagrams) ==
    \* update the chain store with "ChanOpenInit" datagrams
    LET chanOpenInitStore == HandleChanOpenInit(chainID, store, datagrams) IN

    \* update the chain store with "ChanOpenTry" datagrams
    LET chanOpenTryStore == HandleChanOpenTry(chainID, chanOpenInitStore, datagrams) IN

    \* update the chain store with "ChanOpenAck" datagrams
    LET chanOpenAckStore == HandleChanOpenAck(chainID, chanOpenTryStore, datagrams) IN

    \* update the chain store with "ChanOpenConfirm" datagrams
    LET chanOpenConfirmStore == HandleChanOpenConfirm(chainID, chanOpenAckStore, datagrams) IN

    \* update the chain store with "ChanCloseInit" datagrams
    LET chanCloseInitStore == HandleChanCloseInit(chainID, chanOpenConfirmStore, datagrams) IN

    \* update the chain store with "ChanCloseConfirm" datagrams
    LET chanCloseConfirmStore == HandleChanCloseConfirm(chainID, chanCloseInitStore, datagrams) IN

    chanCloseConfirmStore

(***************************************************************************
 Packet update operators
 ***************************************************************************)
\* Update the chain store of the chain with chainID and the packet log, 
\* using the packet datagrams generated by the relayer
\* (Handler operators defined in ICS04PacketHandlers.tla)    
PacketUpdate(chainID, store, packetDatagrams, log) ==
    \* if the sequence of packet datagrams is not empty
    IF packetDatagrams /= AsSeqPacketDatagrams(<<>>)
    THEN \* process the packet datagram at the head of the sequence
         LET packetDatagram == AsPacketDatagram(Head(packetDatagrams)) IN
         LET packet == packetDatagram.packet IN
         \* get the new updated store and packet log entry
         LET newStoreAndLog == 
                IF packetDatagram.type = "PacketRecv"
                THEN HandlePacketRecv(chainID, store, packetDatagram, log)
                ELSE IF packetDatagram.type = "PacketAck"
                     THEN HandlePacketAck(chainID, store, packetDatagram, log)
                     ELSE [chainStore|-> store, packetLogEntry |-> log] IN
         newStoreAndLog
    ELSE [chainStore |-> store, packetLog |->log]

(***************************************************************************
 Chain update operators
 ***************************************************************************)
\* Update chainID with the received datagrams
\* Supports ICS02 (Clients), ICS03 (Connections), and ICS04 (Channels & Packets).
UpdateChainStoreAndPacketLog(chainID, datagrams, packetDatagrams, log) == 
    
    \* ICS02: Client updates
    LET clientUpdatedStore == LightClientUpdate(chainID, chainStore, datagrams) IN

    \* ICS03: Connection updates
    LET connectionUpdatedStore == ConnectionUpdate(chainID, clientUpdatedStore, datagrams) IN

    \* ICS04: Channel updates
    LET channelUpdatedStore == ChannelUpdate(chainID, connectionUpdatedStore, datagrams) IN

    \* ICS04: Packet transmission
    LET packetUpdatedStoreAndLog == PacketUpdate(chainID, channelUpdatedStore, packetDatagrams, log) IN
    LET packetUpdatedStore == packetUpdatedStoreAndLog.chainStore IN

    \* update height
    LET updatedChainStore == 
        IF /\ chainStore /= packetUpdatedStore
           /\ chainStore.height + 1 \in Heights 
        THEN [packetUpdatedStore EXCEPT !.height = chainStore.height + 1]
        ELSE packetUpdatedStore
    IN

    [chainStore |-> updatedChainStore, 
     packetLog |-> packetUpdatedStoreAndLog.packetLog]

(***************************************************************************
 Chain actions
 ***************************************************************************)       
\* Advance the height of the chain until MaxHeight is reached
AdvanceChain ==
    /\ chainStore.height + 1 \in Heights
    /\ chainStore' = [chainStore EXCEPT !.height = chainStore.height + 1]
    /\ UNCHANGED <<incomingDatagrams, incomingPacketDatagrams, history>>
    /\ UNCHANGED <<packetLog, appPacketSeq>>

\* Send a packet
SendPacket ==   
    \* enabled if appPacketSeq is not bigger than MaxPacketSeq 
    /\ appPacketSeq <= MaxPacketSeq
    \* Create a packet: Abstract away from packet data, ports, and timestamp. 
    \* Assume timeoutHeight is MaxHeight + 1
    /\ LET packet == AsPacket([
        sequence |-> appPacketSeq,
        timeoutHeight |-> MaxHeight + 1,
        srcPortID |-> chainStore.connectionEnd.channelEnd.portID,
        srcChannelID |-> chainStore.connectionEnd.channelEnd.channelID,
        dstPortID |-> chainStore.connectionEnd.channelEnd.counterpartyPortID,
        dstChannelID |-> chainStore.connectionEnd.channelEnd.counterpartyChannelID]) IN
        \* update chain store with packet committment
        /\ chainStore' = WritePacketCommitment(chainStore, packet)
        \* log sent packet
        /\ packetLog' = Append(packetLog, AsPacketLogEntry([
                                                type |-> "PacketSent", 
                                                srcChainID |-> ChainID,  
                                                sequence |-> packet.sequence,
                                                timeoutHeight |-> packet.timeoutHeight]))
        \* increase application packet sequence
        /\ appPacketSeq' = appPacketSeq + 1
        /\ UNCHANGED <<incomingDatagrams, incomingPacketDatagrams, history>>

\* write a packet acknowledgement on the packet log and chain store
AcknowledgePacket ==
    /\ chainStore.packetsToAcknowledge /= AsSeqPacket(<<>>)
    /\ chainStore' = WriteAcknowledgement(chainStore, Head(chainStore.packetsToAcknowledge))
    /\ packetLog' = LogAcknowledgement(ChainID, chainStore, packetLog, Head(chainStore.packetsToAcknowledge))
    /\ UNCHANGED <<incomingDatagrams, incomingPacketDatagrams, history>>
    /\ UNCHANGED appPacketSeq

\* Handle the datagrams and update the chain state        
HandleIncomingDatagrams ==
    /\ \/ incomingDatagrams /= AsSetDatagrams({})
       \/ incomingPacketDatagrams /= AsSeqPacketDatagrams(<<>>) 
    /\ LET updatedChainStoreAndPacketLog == UpdateChainStoreAndPacketLog(ChainID, incomingDatagrams, incomingPacketDatagrams, packetLog) IN
        /\ chainStore' = updatedChainStoreAndPacketLog.chainStore
        /\ packetLog' = updatedChainStoreAndPacketLog.packetLog 
        /\ incomingDatagrams' = AsSetDatagrams({})
        /\ incomingPacketDatagrams' = IF incomingPacketDatagrams /= AsSeqPacketDatagrams(<<>>)
                                      THEN Tail(incomingPacketDatagrams)
                                      ELSE incomingPacketDatagrams
        /\ history' = CASE chainStore'.connectionEnd.state = "INIT" 
                                    -> [history EXCEPT !.connInit = TRUE]
                            [] chainStore'.connectionEnd.state = "TRYOPEN"
                                    -> [history EXCEPT !.connTryOpen = TRUE] 
                            [] chainStore'.connectionEnd.state = "OPEN"
                                    -> [history EXCEPT !.connOpen = TRUE] 
                            [] chainStore'.connectionEnd.channelEnd.state = "INIT"
                                    -> [history EXCEPT !.chanInit = TRUE]
                            [] chainStore'.connectionEnd.channelEnd.state = "TRYOPEN"
                                    -> [history EXCEPT !.chanTryOpen = TRUE]
                            [] chainStore'.connectionEnd.channelEnd.state = "OPEN"
                                    -> [history EXCEPT !.chanOpen = TRUE]
                            [] chainStore'.connectionEnd.channelEnd.state = "CLOSED"
                                    -> [history EXCEPT !.chanClosed = TRUE] 
                            [] OTHER 
                                    -> history
        /\ UNCHANGED appPacketSeq

(***************************************************************************
 Specification
 ***************************************************************************)
\* Initial state predicate
\* Initially
\*  - each chain is initialized to some element of the set
\*    InitChainStores (defined in RelayerDefinitions.tla)
\*  - pendingDatagrams for each chain is empty
\*  - the packetSeq is set to 1
Init == 
    /\ chainStore \in InitChainStore(MaxVersion, ChannelOrdering)
    /\ incomingDatagrams = AsSetDatagrams({})
    /\ incomingPacketDatagrams = AsSeqDatagrams(<<>>)
    /\ history = InitHistory
    /\ appPacketSeq = AsInt(1)

\* Next state action
\* The chain either
\*  - advances its height
\*  - receives datagrams and updates its state
\*  - sends a packet if the appPacketSeq is not bigger than MaxPacketSeq
\*  - acknowledges a packet
Next ==
    \/ AdvanceChain 
    \/ HandleIncomingDatagrams
    \/ SendPacket
    \/ AcknowledgePacket
    \/ UNCHANGED vars
        
Fairness ==
    /\ WF_vars(AdvanceChain)
    /\ WF_vars(HandleIncomingDatagrams)        
        
(***************************************************************************
 Invariants
 ***************************************************************************)
\* Type invariant   
\* ChainStores and Datagrams are defined in RelayerDefinitions.tla        
TypeOK ==    
    /\ chainStore \in ChainStores(MaxHeight, ChannelOrdering, MaxPacketSeq, MaxVersion)
    /\ incomingDatagrams \in SUBSET Datagrams(MaxHeight, MaxPacketSeq, MaxVersion)
    /\ history \in Histories
    /\ appPacketSeq \in 1..MaxPacketSeq
    /\ packetLog \in SUBSET Packets(MaxHeight, MaxPacketSeq)
    
(***************************************************************************
 Properties
 ***************************************************************************)    
\* it ALWAYS holds that the height of the chain does not EVENTUALLY decrease
HeightDoesntDecrease ==
    [](\A h \in Heights : chainStore.height = h 
        => <>(chainStore.height >= h))

=============================================================================
\* Modification History
\* Last modified Mon Nov 30 16:50:09 CET 2020 by ilinastoilkovska
\* Created Fri Jun 05 16:56:21 CET 2020 by ilinastoilkovska
