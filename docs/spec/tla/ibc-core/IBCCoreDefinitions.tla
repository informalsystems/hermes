------------------------ MODULE IBCCoreDefinitions -------------------------

(***************************************************************************
 This module contains definitions of operators that are shared between the 
 different modules.
 ***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences

(************************ TYPE ALIASES FOR SNOWCAT *************************)
(* @typeAlias: CHAN = 
    [
        state: Str, 
        order: Str, 
        portID: Str, 
        channelID: Str, 
        counterpartyPortID: Str, 
        counterpartyChannelID: Str, 
        nextSendSeq: Int, 
        nextRcvSeq: Int, 
        nextAckSeq: Int
    ]; 
*)
(* @typeAlias: CONN = 
    [
        state: Str, 
        connectionID: Str, 
        clientID: Str, 
        counterpartyConnectionID: Str, 
        counterpartyClientID: Str, 
        channelEnd: CHAN, 
        versions: Set(Int)
    ]; 
*)
(* @typeAlias: PACKET = 
    [
        sequence: Int,
        timeoutHeight: Int,
        srcPortID: Str,
        srcChannelID: Str, 
        dstPortID: Str,
        dstChannelID: Str
    ]; 
*)
(* @typeAlias: PACKETCOMM = 
    [
        portID: Str, 
        channelID: Str,
        sequence: Int,
        timeoutHeight: Int
    ]; 
*)   
(* @typeAlias: PACKETREC = 
    [
        portID: Str, 
        channelID: Str,
        sequence: Int
    ]; 
*)   
(* @typeAlias: PACKETACK = 
    [
        portID: Str, 
        channelID: Str,
        sequence: Int,
        acknowledgement: Bool
    ]; 
*)  
(* @typeAlias: CHAINSTORE = 
    [
        height: Int, 
        counterpartyClientHeights: Set(Int), 
        connectionEnd: CONN, 
        packetCommitments: Set(PACKETCOMM), 
        packetsToAcknowledge: Seq(PACKET), 
        packetReceipts: Set(PACKETREC),
        packetAcknowledgements: Set(PACKETACK)
    ]; 
*)   
(* @typeAlias: DATAGRAM = 
    [
        type: Str, 
        height: Int, 
        proofHeight: Int, 
        consensusHeight: Int, 
        clientID: Str, 
        counterpartyClientID: Str, 
        connectionID: Str, 
        counterpartyConnectionID: Str, 
        versions: Set(Int), 
        portID: Str, 
        channelID: Str, 
        counterpartyPortID: Str, 
        counterpartyChannelID: Str, 
        packet: PACKET, 
        acknowledgement: Bool
    ]; 
*)
(* @typeAlias: LOGENTRY = 
    [
        type: Str, 
        srcChainID: Str, 
        sequence: Int, 
        timeoutHeight: Int, 
        acknowledgement: Bool
    ]; 
*)
(* @typeAlias: HISTORY = 
    [
        connInit: Bool, 
        connTryOpen: Bool, 
        connOpen: Bool, 
        chanInit: Bool, 
        chanTryOpen: Bool, 
        chanOpen: Bool, 
        chanClosed: Bool
    ];
*)            

(********************** Common operator definitions ***********************)
ChainIDs == {"chainA", "chainB"} 
ClientIDs == {"clA", "clB"}
ConnectionIDs == {"connAtoB", "connBtoA"}
ChannelIDs == {"chanAtoB", "chanBtoA"}
PortIDs == {"portA", "portB"}

nullHeight == 0
nullClientID == "none"
nullConnectionID == "none"
nullChannelID == "none"
nullPortID == "none"

ConnectionStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN"}
ChannelStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN", "CLOSED"}
ChannelOrder == {"ORDERED", "UNORDERED"} 

Max(S) == CHOOSE x \in S: \A y \in S: y <= x 
Min(S) == CHOOSE x \in S: \A y \in S: y >= x 

(******************************* ChannelEnds *******************************
    A set of channel end records. 
    A channel end record contains the following fields:
    
    - state -- a string 
      Stores the current state of this channel end. It has one of the 
      following values: "UNINIT", "INIT", "TRYOPEN", "OPEN", "CLOSED".
      
    - order -- a string
      Stores whether the channel end is ordered or unordered. It has one 
      of the following values: "UNORDERED", "ORDERED".
        
        * ordered channels have three additional packet sequence fields:
           nextSendSeq -- stores the sequence number of the next packet that 
           is going to be sent,
           nextRcvSeq -- stores the sequence number of the next packet that 
           is going to be received,
           nextAckSeq -- stores the sequence number of the next packet that 
           is going to be acknowledged.
    
    - portID -- a port identifier
      Stores the port identifier of this channel end.  
    
    - channelID -- a channel identifier
      Stores the channel identifier of this channel end.  
    
    - counterpartyPortID -- a port identifier
      Stores the port identifier of the counterparty channel end.   
    
    - counterpartyChannelID -- a channel identifier
      Stores the channel identifier of the counterparty channel end. 
      
    Note: we omit channel versions and connection hops.
 ***************************************************************************)   
ChannelEnds(channelOrdering, maxPacketSeq) ==
    IF channelOrdering = "UNORDERED"
    THEN \* set of unordered channels
         [
             state : ChannelStates,
             order : {"UNORDERED"}, 
             portID : PortIDs \union {nullPortID},
             channelID : ChannelIDs \union {nullChannelID},
             counterpartyPortID : PortIDs \union {nullPortID},
             counterpartyChannelID : ChannelIDs \union {nullChannelID}
         ] 
    ELSE \* set of ordered channels
         [
             state : ChannelStates,
             order : {"ORDERED"},
             nextSendSeq : 0..maxPacketSeq,
             nextRcvSeq : 0..maxPacketSeq,
             nextAckSeq : 0..maxPacketSeq, 
             portID : PortIDs \union {nullPortID},
             channelID : ChannelIDs \union {nullChannelID},
             counterpartyPortID : PortIDs \union {nullPortID},
             counterpartyChannelID : ChannelIDs \union {nullChannelID}
         ] 
    
    
(******* PacketCommitments, PacketReceipts, PacketAcknowledgements *********)
\* Set of packet commitments
PacketCommitments(Heights, maxPacketSeq) ==
    [
        portID : PortIDs,
        channelID : ChannelIDs, 
        sequence : 1..maxPacketSeq, 
        timeoutHeight : Heights
    ] 
    
\* Set of packet receipts
PacketReceipts(maxPacketSeq) ==
    [
        portID : PortIDs,
        channelID : ChannelIDs, 
        sequence : 1..maxPacketSeq
    ] 
    
\* Set of packet acknowledgements    
PacketAcknowledgements(maxPacketSeq) ==
    [
        portID : PortIDs,
        channelID : ChannelIDs, 
        sequence : 1..maxPacketSeq,
        acknowledgement : BOOLEAN
    ] 

(***************************** ConnectionEnds *****************************
    A set of connection end records. 
    A connection end record contains the following fields:
    
    - state -- a string 
      Stores the current state of this connection end. It has one of the 
      following values: "UNINIT", "INIT", "TRYOPEN", "OPEN".
    
    - connectionID -- a connection identifier
      Stores the connection identifier of this connection end.
    
    - counterpartyConnectionID -- a connection identifier
      Stores the connection identifier of the counterparty connection end.
    
    - clientID -- a client identifier
      Stores the client identifier associated with this connection end. 
      
    - counterpartyClientID -- a client identifier
      Stores the counterparty client identifier associated with this connection end.

    - versions -- a set of versions
      Stores the set of supported connection versions. At the end of a handshake, 
      it should be a singleton set.
      
    - channelEnd : a channel end record 
      Stores data about the channel associated with this connection end.  
 ***************************************************************************)
ConnectionEnds(channelOrdering, maxPacketSeq, Versions) ==
    [
        state : ConnectionStates,
        connectionID : ConnectionIDs \union {nullConnectionID},
        counterpartyConnectionID : ConnectionIDs \union {nullConnectionID},
        clientID : ClientIDs \union {nullClientID},
        counterpartyClientID : ClientIDs \union {nullClientID},
        versions : (SUBSET Versions) \ {{}}, 
        channelEnd : ChannelEnds(channelOrdering, maxPacketSeq)
    ] 
    
(********************************* Packets *********************************)
\* Set of packets
Packets(Heights, maxPacketSeq) ==
    [
        sequence : 1..maxPacketSeq,
        timeoutHeight : Heights,
        srcPortID : PortIDs,
        srcChannelID : ChannelIDs,
        dstPortID : PortIDs,
        dstChannelID : ChannelIDs
    ] 

(******************************** ChainStores ******************************
    A set of chain store records. 
    A chain store record contains the following fields:
    
    - height : an integer between nullHeight and MaxHeight. 
      Stores the current height of the chain.
    
    - counterpartyClientHeights : a set of integers between 1 and MaxHeight
      Stores the heights of the client for the counterparty chain.

    - connectionEnd : a connection end record 
      Stores data about the connection with the counterparty chain.

    - packetCommitments : a set of packet commitments
      A packet commitment is added to this set when a chain sends a packet 
      to the counterparty.

    - packetReceipts : a set of packet receipts
      A packet receipt is added to this set when a chain received a packet 
      from the counterparty chain.
    
    - packetsToAcknowledge : a sequence of packets
      A packet is added to this sequence when a chain receives it and is used 
      later for the receiver chain to write an acknowledgement for the packet. 
    
    - packetAcknowledgements : a set of packet acknowledgements
      A packet acknowledgement is added to this set when a chain writes an 
      acknowledgement for a packet it received from the counterparty.
        
    A chain store is the combination of the provable and private stores.
 ***************************************************************************)
ChainStores(Heights, channelOrdering, maxPacketSeq, Versions) ==    
    [
        height : Heights,
        counterpartyClientHeights : SUBSET(Heights),
        connectionEnd : ConnectionEnds(channelOrdering, maxPacketSeq, Versions),
        packetCommitments : SUBSET(PacketCommitments(Heights, maxPacketSeq)),
        packetReceipts : SUBSET(PacketReceipts(maxPacketSeq)), 
        packetsToAcknowledge : Seq(Packets(Heights, maxPacketSeq)),
        packetAcknowledgements : SUBSET(PacketAcknowledgements(maxPacketSeq))
    ] 

(******************************** Datagrams ********************************)
\* Set of datagrams
Datagrams(Heights, maxPacketSeq, Versions) ==
    [
        type : {"ClientCreate"}, 
        clientID : ClientIDs, 
        height : Heights
    ] \union [
        type : {"ClientUpdate"}, 
        clientID : ClientIDs, 
        height : Heights
    ] \union [
        type : {"ConnOpenInit"}, 
        connectionID : ConnectionIDs, 
        counterpartyConnectionID : ConnectionIDs, 
        clientID : ClientIDs, 
        counterpartyClientID : ClientIDs
    ] \union [
        type : {"ConnOpenTry"}, 
        desiredConnectionID : ConnectionIDs, 
        counterpartyConnectionID : ConnectionIDs, 
        clientID : ClientIDs, 
        counterpartyClientID : ClientIDs, 
        versions : SUBSET (Versions), 
        proofHeight : Heights, 
        consensusHeight : Heights
    ] \union [
        type : {"ConnOpenAck"}, 
        connectionID : ConnectionIDs,
        versions : SUBSET (Versions), 
        proofHeight : Heights, 
        consensusHeight : Heights
    ] \union [
        type : {"ConnOpenConfirm"}, 
        connectionID : ConnectionIDs, 
        proofHeight : Heights
    ] \union [
        type : {"ChanOpenInit"}, 
        portID : PortIDs,
        channelID : ChannelIDs,
        counterpartyPortID : PortIDs, 
        counterpartyChannelID : ChannelIDs
    ] \union [
        type : {"ChanOpenTry"}, 
        portID : PortIDs,
        channelID : ChannelIDs, 
        counterpartyPortID : PortIDs,
        counterpartyChannelID : ChannelIDs, 
        proofHeight : Heights
    ] \union [
        type : {"ChanOpenAck"}, 
        portID : PortIDs,
        channelID : ChannelIDs, 
        proofHeight : Heights
    ] \union [
        type : {"ChanOpenConfirm"}, 
        portID : PortIDs,
        channelID : ChannelIDs, 
        proofHeight : Heights
    ] \union [
        type : {"ChanCloseInit"}, 
        portID : PortIDs,
        channelID : ChannelIDs
    ] \union [
        type : {"ChanCloseConfirm"},
        portID : PortIDs, 
        channelID : ChannelIDs, 
        proofHeight : Heights
    ] \union [
        type : {"PacketRecv"}, 
        packet : Packets(Heights, maxPacketSeq), 
        proofHeight : Heights
    ] \union [
        type : {"PacketAck"}, 
        packet : Packets(Heights, maxPacketSeq), 
        acknowledgement : BOOLEAN, 
        proofHeight : Heights
    ]
  
\* Null datagram  
NullDatagram == 
    [type |-> "null"] 
    
(**************************** PacketLogEntries *****************************)
\* Set of packet log entries
PacketLogEntries(Heights, maxPacketSeq) == 
    [
        type : {"PacketSent"},
        srcChainID : ChainIDs,  
        sequence : 1..maxPacketSeq,
        timeoutHeight : Heights
    ] \union [
        type : {"PacketRecv"},
        srcChainID : ChainIDs,  
        sequence : 1..maxPacketSeq,
        portID : PortIDs,
        channelID : ChannelIDs,
        timeoutHeight : Heights
    ] \union [
        type : {"WriteAck"},
        srcChainID : ChainIDs,  
        sequence : 1..maxPacketSeq,
        portID : PortIDs,
        channelID : ChannelIDs,
        timeoutHeight : Heights,
        acknowledgement : BOOLEAN
    ]

\* Null packet log entry
NullPacketLogEntry ==
    [type |-> "null"] 

(******************************* Histories ********************************)
\* Set of history variable records
Histories ==
    [
        connInit : BOOLEAN,
        connTryOpen : BOOLEAN, 
        connOpen : BOOLEAN,
        chanInit : BOOLEAN,
        chanTryOpen : BOOLEAN,
        chanOpen : BOOLEAN,
        chanClosed : BOOLEAN
     ] 

(***************************************************************************
 Initial values of a channel end, connection end, chain
 ***************************************************************************)
\* Initial value of an unordered channel end:
\*      - state is "UNINIT"
\*      - order is "UNORDERED"
\*      - channelID, counterpartyPortID, counterpartyChannelID are uninitialized
InitUnorderedChannelEnd ==
    [
        state |-> "UNINIT",
        order |-> "UNORDERED",
        portID |-> nullPortID,
        channelID |-> nullChannelID,
        counterpartyPortID |-> nullPortID,
        counterpartyChannelID |-> nullChannelID
    ] 
     
\* Initial value of an ordered channel end:
\*      - state is "UNINIT"
\*      - order is "ORDERED"
\*      - nextSendSeq, nextRcvSeq, nextAckSeq are set to 0
\*      - channelID, counterpartyPortID, counterpartyChannelID are uninitialized
InitOrderedChannelEnd ==
    [   
        state |-> "UNINIT",
        order |-> "ORDERED",
        nextSendSeq |-> 0,
        nextRcvSeq |-> 0,
        nextAckSeq |-> 0,
        portID |-> nullPortID,
        channelID |-> nullChannelID,
        counterpartyPortID |-> nullPortID,
        counterpartyChannelID |-> nullChannelID
    ] 

\* Initial value of a connection end:
\*      - state is "UNINIT"
\*      - connectionID, counterpartyConnectionID are uninitialized
\*      - clientID, counterpartyClientID are uninitialized  
\*      - versions is an arbitrary (non-empty) subset of the set {1, .., maxVersion}   
\*      - channelEnd is initialized based on channelOrdering      
InitConnectionEnds(Versions, channelOrdering) ==
    IF channelOrdering = "ORDERED"
    THEN [
            state : {"UNINIT"},
            connectionID : {nullConnectionID},
            clientID : {nullClientID},
            counterpartyConnectionID : {nullConnectionID},
            counterpartyClientID : {nullClientID},
            versions : (SUBSET Versions) \ {{}},
            channelEnd : {InitOrderedChannelEnd}
         ]
    ELSE [
            state : {"UNINIT"},
            connectionID : {nullConnectionID},
            clientID : {nullClientID},
            counterpartyConnectionID : {nullConnectionID},
            counterpartyClientID : {nullClientID},
            versions : (SUBSET Versions) \ {{}},
            channelEnd : {InitUnorderedChannelEnd}
         ]   

\* Initial value of the chain store: 
\*      - height is initialized to 1
\*      - the counterparty light client is uninitialized
\*      - the connection end is initialized to InitConnectionEnd 
\*      - the packet committments, receipts, acknowledgements, and 
\*        packets to acknowledge are empty  
InitChainStore(Versions, channelOrdering) == 
    [
        height : {1},
        counterpartyClientHeights : {{}}, 
        connectionEnd : InitConnectionEnds(Versions, channelOrdering),
        
        packetCommitments : {{}},
        packetReceipts : {{}}, 
        packetAcknowledgements : {{}},
        packetsToAcknowledge : {<<>>}
        
    ] 
        
\* Initial value of history flags         
InitHistory ==
     [
        connInit |-> FALSE,
        connTryOpen |-> FALSE, 
        connOpen |-> FALSE,
        chanInit |-> FALSE,
        chanTryOpen |-> FALSE,
        chanOpen |-> FALSE,
        chanClosed |-> FALSE
     ]  
         
(***************************************************************************
 Client helper operators
 ***************************************************************************)

\* get the ID of chainID's counterparty chain    
GetCounterpartyChainID(chainID) ==
    \* IF chainID = "chainA" THEN AsID("chainB") ELSE AsID("chainA")    
    IF chainID = "chainA" THEN "chainB" ELSE "chainA"
 
\* get the client ID of the client for chainID 
GetClientID(chainID) ==
    \* IF chainID = "chainA" THEN AsID("clA") ELSE AsID("clB")
    IF chainID = "chainA" THEN "clA" ELSE "clB"
        
\* get the client ID of the client for chainID's counterparty chain           
GetCounterpartyClientID(chainID) ==
    \* IF chainID = "chainA" THEN AsID("clB") ELSE AsID("clA")
    IF chainID = "chainA" THEN "clB" ELSE "clA"
    
\* get the latest height of chainID
\* @type: (CHAINSTORE) => Int;
GetLatestHeight(chain) ==
    chain.height
      
\* get the maximal height of the client for chainID's counterparty chain    
\* @type: (CHAINSTORE) => Int;
GetMaxCounterpartyClientHeight(chain) ==
    IF chain.counterpartyClientHeights /= {}
    THEN Max(chain.counterpartyClientHeights)
    ELSE nullHeight

\* get the set of heights of the client for chainID's counterparty chain    
\* @type: (CHAINSTORE) => Set(Int);
GetCounterpartyClientHeights(chain) ==
    chain.counterpartyClientHeights

\* returns true if the counterparty client is initialized on chainID
\* @type: (CHAINSTORE) => Bool;
IsCounterpartyClientOnChain(chain) ==
    chain.counterpartyClientHeights /= {}

\* returns true if the height h is in counterparty client heights on chainID 
\* @type: (CHAINSTORE, Int) => Bool;
IsCounterpartyClientHeightOnChain(chain, h) ==
    h \in chain.counterpartyClientHeights
     
(***************************************************************************
 Connection helper operators
 ***************************************************************************)

\* get the connection ID of the connection end at chainID
GetConnectionID(chainID) ==
    IF chainID = "chainA"
    THEN "connAtoB"
    ELSE IF chainID = "chainB"
         THEN "connBtoA"
         ELSE nullConnectionID

\* get the connection ID of the connection end at chainID's counterparty chain
GetCounterpartyConnectionID(chainID) ==
    IF chainID = "chainA"
    THEN "connBtoA"
    ELSE IF chainID = "chainB"
         THEN "connAtoB"
         ELSE nullConnectionID
          
\* get the connection end at chainID
\* @type: (CHAINSTORE) => CONN;
GetConnectionEnd(chain) == 
    chain.connectionEnd
    
\* pick the minimal version from a set of versions
PickVersion(versions) == 
    IF versions /= {}
    THEN LET minVersion == Min(versions) IN
         {minVersion}
    ELSE {}
    

\* returns true if the connection end on chainID is UNINIT
\* @type: (CHAINSTORE) => Bool;
IsConnectionUninit(chain) ==
    chain.connectionEnd.state = "UNINIT"

\* returns true if the connection end on chainID is INIT
\* @type: (CHAINSTORE) => Bool;
IsConnectionInit(chain) ==
    chain.connectionEnd.state = "INIT"

\* returns true if the connection end on chainID is TRYOPEN
\* @type: (CHAINSTORE) => Bool;
IsConnectionTryOpen(chain) ==
    chain.connectionEnd.state = "TRYOPEN"
    
\* returns true if the connection end on chainID is OPEN
\* @type: (CHAINSTORE) => Bool;
IsConnectionOpen(chain) ==
    chain.connectionEnd.state = "OPEN"
          
(***************************************************************************
 Channel helper operators
 ***************************************************************************)

\* get the channel ID of the channel end at the connection end of chainID
GetChannelID(chainID) ==
    IF chainID = "chainA"
    THEN "chanAtoB"
    ELSE IF chainID = "chainB"
         THEN "chanBtoA"
         ELSE nullChannelID
         
\* get the channel ID of the channel end at chainID's counterparty chain
GetCounterpartyChannelID(chainID) ==
    IF chainID = "chainA"
    THEN "chanBtoA"
    ELSE IF chainID = "chainB"
         THEN "chanAtoB"
         ELSE nullChannelID
         
\* get the port ID at chainID
GetPortID(chainID) ==
    IF chainID = "chainA"
    THEN "portA"
    ELSE IF chainID = "chainB"
         THEN "portB"
         ELSE nullPortID
   
\* get the port ID at chainID's counterparty chain
GetCounterpartyPortID(chainID) ==
    IF chainID = "chainA"
    THEN "portB"
    ELSE IF chainID = "chainB"
         THEN "portA"
         ELSE nullPortID
                   
\* get the channel end at the connection end of chainID         
\* @type: (CHAINSTORE) => CHAN;
GetChannelEnd(chain) ==
    chain.connectionEnd.channelEnd
    
\* returns true if the channel end on chainID is UNINIT
\* @type: (CHAINSTORE) => Bool;
IsChannelUninit(chain) ==
    chain.connectionEnd.channelEnd.state = "UNINIT"

\* returns true if the channel end on chainID is INIT
\* @type: (CHAINSTORE) => Bool;
IsChannelInit(chain) ==
    chain.connectionEnd.channelEnd.state = "INIT"

\* returns true if the channel end on chainID is TRYOPEN
\* @type: (CHAINSTORE) => Bool;
IsChannelTryOpen(chain) ==
    chain.connectionEnd.channelEnd.state = "TRYOPEN"
    
\* returns true if the channel end on chainID is OPEN
\* @type: (CHAINSTORE) => Bool;
IsChannelOpen(chain) ==
    chain.connectionEnd.channelEnd.state = "OPEN"    
    
\* returns true if the channel end on chainID is CLOSED
\* @type: (CHAINSTORE) => Bool;
IsChannelClosed(chain) ==
    chain.connectionEnd.channelEnd.state = "CLOSED"                                   

=============================================================================
\* Modification History
\* Last modified Mon Apr 12 14:26:47 CEST 2021 by ilinastoilkovska
\* Created Fri Jun 05 16:56:21 CET 2020 by ilinastoilkovska