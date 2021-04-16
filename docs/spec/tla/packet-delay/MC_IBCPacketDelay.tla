-------------------------- MODULE MC_IBCPacketDelay -------------------------

MaxHeight == 3
ChannelOrdering == "UNORDERED"
MaxPacketSeq == 1
MaxDelay == 1

VARIABLES 
    \* @type: CHAINSTORE;
    chainAstore, \* store of ChainA
    \* @type: CHAINSTORE;
    chainBstore, \* store of ChainB
    \* @type: Seq(DATAGRAM);
    packetDatagramsChainA, \* sequence of packet datagrams incoming to ChainA
    \* @type: Seq(DATAGRAM);
    packetDatagramsChainB, \* sequence of packet datagrams incoming to ChainB
    \* @type: Str -> Seq(DATAGRAM);
    outgoingPacketDatagrams, \* packet datagrams created by the relayer but not submitted
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
