-------------------------- MODULE IBCCore_apalache --------------------------

VARIABLES chainAstore, \* chain store of ChainA
          chainBstore, \* chain store of ChainB
          incomingDatagramsChainA, \* set of (client, connection, channel) datagrams incoming to ChainA
          incomingDatagramsChainB, \* set of (client, connection, channel) datagrams incoming to ChainB
          incomingPacketDatagramsChainA, \* sequence of packet datagrams incoming to ChainA
          incomingPacketDatagramsChainB, \* sequence of packet datagrams incoming to ChainB
          relayer1Heights, \* the client heights of Relayer1
          relayer2Heights, \* the client heights of Relayer2
          outgoingDatagrams, \* sets of (client, connection, channel) datagrams outgoing of the relayers
          outgoingPacketDatagrams, \* sequences of packet datagrams outgoing of the relayers
          closeChannelA, \* flag that triggers closing of the channel end at ChainA
          closeChannelB, \* flag that triggers closing of the channel end at ChainB
          historyChainA, \* history variables for ChainA
          historyChainB, \* history variables for ChainB
          packetLog, \* packet log 
          appPacketSeqChainA, \* packet sequence number from the application on ChainA
          appPacketSeqChainB \* packet sequence number from the application on ChainB

INSTANCE IBCCore WITH
    MaxHeight <- 2,
    MaxVersion <- 2,
    MaxPacketSeq <- 2,
    ClientDatagramsRelayer1 <- TRUE, 
    ClientDatagramsRelayer2 <- TRUE,
    ConnectionDatagramsRelayer1 <- TRUE,
    ConnectionDatagramsRelayer2 <- TRUE,
    ChannelDatagramsRelayer1 <- TRUE,
    ChannelDatagramsRelayer2 <- TRUE,
    PacketDatagramsRelayer1 <- TRUE,
    PacketDatagramsRelayer2 <- TRUE,
    ChannelOrdering <- "UNORDERED"

=============================================================================
\* Modification History
\* Last modified Fri Jan 29 17:34:56 CET 2021 by ilinastoilkovska
\* Created Wed Aug 05 11:27:26 CEST 2020 by ilinastoilkovska
