-------------------------- MODULE MC_IBCPacketDelay -------------------------

MaxHeight == 3
\* @type: Str;
ChannelOrdering == "UNORDERED"
MaxPacketSeq == 1
MaxDelay == 1

VARIABLES 
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
            timestamp: Int,
            counterpartyClientHeights: Int -> Int, 
            channelEnd: CHAN, 
            packetCommitments: Set(PACKETCOMM), 
            packetsToAcknowledge: Seq(PACKET), 
            packetReceipts: Set(PACKETREC),
            packetAcknowledgements: Set(PACKETACK)
        ]; 
    *)
    \* @type: CHAINSTORE;
    chainAstore, \* store of ChainA
    \* @type: CHAINSTORE;
    chainBstore, \* store of ChainB
    (* @typeAlias: DATAGRAM = 
        [
            type: Str, 
            packet: PACKET, 
            proofHeight: Int, 
            acknowledgement: Bool
        ]; 
    *)
    \* @type: Seq(DATAGRAM);
    packetDatagramsChainA, \* sequence of packet datagrams incoming to ChainA
    \* @type: Seq(DATAGRAM);
    packetDatagramsChainB, \* sequence of packet datagrams incoming to ChainB
    \* @type: Str -> Seq(DATAGRAM);
    outgoingPacketDatagrams, \* packet datagrams created by the relayer but not submitted
    (* @typeAlias: LOGENTRY = 
        [
            type: Str, 
            srcChainID: Str, 
            sequence: Int, 
            timeoutHeight: Int, 
            acknowledgement: Bool
        ]; 
    *)
    \* @type: Seq(LOGENTRY);
    packetLog, \* packet log
    \* @type: Int;
    appPacketSeqChainA, \* packet sequence number from the application on ChainA
    \* @type: Int;
    appPacketSeqChainB, \* packet sequence number from the application on ChainB
    \* @type: <<Str, Int>> -> Int;
    packetDatagramTimestamp \* history variable that tracks when packet datagrams were processed

INSTANCE IBCPacketDelay

=============================================================================
