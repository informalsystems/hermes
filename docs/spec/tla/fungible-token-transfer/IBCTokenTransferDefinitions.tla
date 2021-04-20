-------------------- MODULE IBCTokenTransferDefinitions --------------------

(***************************************************************************
 This module contains definitions of operators that are shared between the 
 different modules, and which are relevant for ICS20.
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
        version: Str
    ]; 
*)
(* @typeAlias: PACKETDATA =
    [
        denomination: Seq(Str),
        amount: Int,
        sender: Str,
        receiver: Str
    ];
*)
(* @typeAlias: PACKET = 
    [
        sequence: Int,
        timeoutHeight: Int,
        data: PACKETDATA,
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
        data: PACKETDATA,
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
(* @typeAlias: ACCOUNT =
    <<Str, Seq(Str)>>;
*)
(* @typeAlias: PACKETTOACK =
    <<PACKET, Bool>>;    
*)
(* @typeAlias: CHAINSTORE = 
    [
        height: Int, 
        counterpartyClientHeights: Set(Int), 
        channelEnd: CHAN, 
        packetCommitments: Set(PACKETCOMM), 
        packetsToAcknowledge: Seq(PACKETTOACK), 
        packetReceipts: Set(PACKETREC),
        packetAcknowledgements: Set(PACKETACK),
        escrowAccounts: ACCOUNT -> Int
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
        acknowledgement: Bool,
        data: PACKETDATA
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
ChannelIDs == {"chanAtoB", "chanBtoA"}
PortIDs == {"portA", "portB"}
ChannelStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN", "CLOSED"}

nullHeight == 0
nullChannelID == "none"
nullPortID == "none"
nullEscrowAddress == "none"

Max(S) == CHOOSE x \in S: \A y \in S: y <= x 

(******************************* ChannelEnds *******************************
    A set of channel end records. 
    A channel end record contains the following fields:
    
    - state -- a string 
      Stores the current state of this channel end. It has one of the 
      following values: "UNINIT", "INIT", "TRYOPEN", "OPEN", "CLOSED".
      
    - order -- a string
      Stores whether the channel end is ordered or unordered. It has one of the 
      following values: "UNORDERED", "ORDERED"
        
        * for ICS20 we require that the channels are unordered
      
    - portID -- a port identifier
      Stores the port identifier of this channel end.  
        
    - channelID -- a channel identifier
      Stores the channel identifier of this channel end.  
      
    - counterpartyPortID -- a port identifier
      Stores the port identifier of the counterparty channel end.     
    
    - counterpartyChannelID -- a channel identifier
      Stores the channel identifier of the counterparty channel end. 
      
    - version -- a string
      The version is "ics20-1" for fungible token transfer
 ***************************************************************************)       
    
ChannelEnds ==
    [
        state : ChannelStates,
        order : {"UNORDERED"}, 
        portID : PortIDs \union {nullPortID},
        channelID : ChannelIDs \union {nullChannelID},
        counterpartyPortID : PortIDs \union {nullPortID},
        counterpartyChannelID : ChannelIDs \union {nullChannelID},
        version : {"ics20-1"}
    ] 

(************************* FungibleTokenPacketData *************************
 A set of records defining ICS20 packet data.
 
 Denominations are defined as Seq(ChannelIDs \union PortIDs \union NativeDenominations), 
 where NativeDenominations is the set of native denominations of the two chains.
 ***************************************************************************)    
\* @type: (Int, Set(Seq(Str))) => Set(PACKETDATA);
FungibleTokenPacketData(maxBalance, Denominations) ==
    [
        denomination : Denominations,
        amount : 0..maxBalance,
        sender : ChainIDs,
        receiver : ChainIDs
    ]
    
(******* PacketCommitments, PacketReceipts, PacketAcknowledgements *********)
\* Set of packet commitments
\* @type: (Set(Int), Int, Int, Set(Seq(Str))) => Set(PACKETCOMM);
PacketCommitments(Heights, maxPacketSeq, maxBalance, Denominations) ==
    [
        channelID : ChannelIDs,
        portID : PortIDs, 
        sequence : 1..maxPacketSeq,
        data : FungibleTokenPacketData(maxBalance, Denominations),
        timeoutHeight : Heights
    ] 

\* Set of packet receipts
\* @type: (Int) => Set(PACKETREC);
PacketReceipts(maxPacketSeq) ==
    [
        channelID : ChannelIDs, 
        portID : PortIDs, 
        sequence : 1..maxPacketSeq
    ] 

\* Set of packet acknowledgements    
\* @type: (Int) => Set(PACKETACK);
PacketAcknowledgements(maxPacketSeq) ==
    [
        channelID : ChannelIDs, 
        portID : PortIDs, 
        sequence : 1..maxPacketSeq,
        acknowledgement : BOOLEAN
    ] 
    
(********************************* Packets *********************************)
\* Set of packets
\* @type: (Set(Int), Int, Int, Set(Seq(Str))) => Set(PACKET);
Packets(Heights, maxPacketSeq, maxBalance, Denominations) ==
    [
        sequence : 1..maxPacketSeq,
        timeoutHeight : Heights,
        data : FungibleTokenPacketData(maxBalance, Denominations),
        srcPortID : PortIDs,
        srcChannelID : ChannelIDs,
        dstPortID : PortIDs,
        dstChannelID : ChannelIDs
    ] 

(******************************** ChainStores ******************************
    A set of chain store records, with fields relevant for ICS20. 
    A chain store record contains the following fields:
    
    - height : an integer between nullHeight and MaxHeight. 
      Stores the current height of the chain.
      
    - counterpartyClientHeights : a set of integers between 1 and MaxHeight
      Stores the heights of the client for the counterparty chain.  
    
    - channelEnd : a channel end
      Stores data about the channel with the counterparty chain.    
    
    - packetCommitments : a set of packet commitments
      A packet commitment is added to this set when a chain sends a packet 
      to the counterparty.

    - packetReceipts : a set of packet receipts
      A packet receipt is added to this set when a chain received a packet 
      from the counterparty chain.

    - packetAcknowledgements : a set of packet acknowledgements
      A packet acknowledgement is added to this set when a chain writes an 
      acknowledgement for a packet it received from the counterparty

    - packetsToAcknowledge : a sequence of pairs <<packet, ack>>
      A pair <<packet, ack>>, where ack is a Boolean value, is added 
      to this sequence when a chain successfully receives a PacketRecv 
      datagram      
    
    A chain store is the combination of the provable and private stores.
      
 ***************************************************************************)
\* @type: (Set(Int), Int, Int, Set(Str)) => Set(CHAINSTORE);
ChainStores(Heights, maxPacketSeq, maxBalance, NativeDenominations) ==    
    [
        height : Heights,
        counterpartyClientHeights : SUBSET(Heights),
        channelEnd : ChannelEnds,
        
        packetCommitments : SUBSET(PacketCommitments(Heights, maxPacketSeq, maxBalance, 
                                           Seq(ChannelIDs \union PortIDs \union NativeDenominations))),
        packetReceipts : SUBSET(PacketReceipts(maxPacketSeq)),
        packetAcknowledgements : SUBSET(PacketAcknowledgements(maxPacketSeq)),
        packetsToAcknowledge : Seq(Packets(Heights, maxPacketSeq, maxBalance, 
                                           Seq(ChannelIDs \union PortIDs \union NativeDenominations))
                                   \X
                                   BOOLEAN)
    ] 
    
(******************************** Datagrams ********************************)
\* Set of datagrams
Datagrams(Heights, maxPacketSeq, maxBalance, NativeDenominations) ==
    [type : {"PacketRecv"}, 
     packet : Packets(Heights, maxPacketSeq, maxBalance, 
                      Seq(ChannelIDs \union PortIDs \union NativeDenominations)), 
     proofHeight : Heights]
    \union 
    [type : {"PacketAck"}, 
     packet : Packets(Heights, maxPacketSeq, maxBalance, 
                      Seq(ChannelIDs \union PortIDs \union NativeDenominations)), 
     acknowledgement : BOOLEAN, 
     proofHeight : Heights]
          
\* Null datagram
NullDatagram == 
    [type |-> "null"] 
    
(**************************** PacketLogEntries *****************************)
\* Set of packet log entries
PacketLogEntries(Heights, maxPacketSeq, maxBalance, NativeDenominations) == 
    [
        type : {"PacketSent"},
        srcChainID : ChainIDs,  
        sequence : 1..maxPacketSeq,
        timeoutHeight : Heights,
        data : FungibleTokenPacketData(maxBalance, 
                                       Seq(ChannelIDs \union PortIDs \union NativeDenominations))
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
        data : FungibleTokenPacketData(maxBalance, 
                                       Seq(ChannelIDs \union PortIDs \union NativeDenominations)),
        acknowledgement : BOOLEAN
    ] 
    
(***************************************************************************
 Chain helper operators
 ***************************************************************************)

\* get the ID of chainID's counterparty chain    
GetCounterpartyChainID(chainID) ==
    IF chainID = "chainA" THEN "chainB" ELSE "chainA"
      
\* get the maximal height of the client for chainID's counterparty chain   
\* @type: (CHAINSTORE) => Int;
GetMaxCounterpartyClientHeight(chain) ==
    IF chain.counterpartyClientHeights /= {}
    THEN Max(chain.counterpartyClientHeights)
    ELSE nullHeight

\* get the channel ID of the channel end at chainID
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

\* get the latest height of chain
\* @type: (CHAINSTORE) => Int;
GetLatestHeight(chain) ==
    chain.height

(***************************************************************************
 Initial values of a channel end, chain store, accounts for ICS20
 ***************************************************************************)
\* Initial value of a channel end:
\*      - state is "OPEN" (we assume channel handshake has successfully finished)
\*      - order is "UNORDERED" (requirement of ICS20)
\*      - channelID, counterpartyChannelID 
InitUnorderedChannelEnd(ChainID) ==
    [
        state |-> "OPEN",
        order |-> "UNORDERED",
        portID |-> GetPortID(ChainID),
        channelID |-> GetChannelID(ChainID),
        counterpartyPortID |-> GetCounterpartyPortID(ChainID),
        counterpartyChannelID |-> GetCounterpartyChannelID(ChainID),
        version |-> "ics20-1"
    ] 

\* A set of initial values of the chain store for ICS20: 
\*      - height is initialized to 1
\*      - counterpartyClientHeights is the set of installed client heights 
\*      - the channelEnd is initialized to InitUnorderedChannelEnd
\*      - the packet committments, receipts, acknowledgements, and packets  
\*        to acknowledge are empty
ICS20InitChainStore(ChainID) == 
    [
        height |-> 1,
        counterpartyClientHeights |-> {}, 
        channelEnd |-> InitUnorderedChannelEnd(ChainID),
        
        packetCommitments |-> {},
        packetReceipts |-> {},
        packetAcknowledgements |-> {},
        packetsToAcknowledge |-> <<>>
    ] 

=============================================================================
\* Modification History
\* Last modified Wed Apr 14 15:27:35 CEST 2021 by ilinastoilkovska
\* Created Mon Oct 17 13:01:38 CEST 2020 by ilinastoilkovska
