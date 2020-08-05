--------------------------- MODULE PacketHandlers ---------------------------

(***************************************************************************
 This module contains definitions of operators that are used to handle
 packet datagrams
 ***************************************************************************)

EXTENDS Integers, FiniteSets, RelayerDefinitions    

(***************************************************************************
 Packet datagram handlers
 ***************************************************************************)

\* Handle "PacketRecv" datagrams
HandlePacketRecv(chainID, chain, datagrams) ==
    \* get chainID's connection end
    LET connectionEnd == chain.connectionEnd IN
    \* get chainID's channel end
    LET channelEnd == chain.connectionEnd.channelEnd IN
    \* get valid "PacketRecv" datagrams
    LET packetRecvDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "PacketRecv"
                            /\ dgr.srcChannelID = GetChannelID(chainID)
                            /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
                                
    IF \* if there are valid "PacketRecv" datagrams 
       /\ packetRecvDgrs /= {} 
       \* and the channel and connection ends are open for packet transmission, then
       /\ channelEnd.state \notin {"UNINIT", "CLOSED"}
       /\ connectionEnd.state /= "UNINIT"
    \* get the packets               
    THEN LET packets == {dgr.packet : dgr \in packetRecvDgrs} IN
         \* if there are packets that have not passed the timeout height
         IF \E packet \in packets : packet.timeoutHeight < chain.height
         THEN \* pick a packet that has not passed the timeout height
              LET packet == CHOOSE p \in packets : p.timeoutHeight < chain.height IN
              \* if the channel is unordered or 
              \* if it is ordered and the packet sequence is nextRcvSeq, update the chain store 
              IF \/ channelEnd.order = "UNORDERED" 
                 \/ /\ channelEnd.order = "ORDERED"
                    /\ packet.sequence = channelEnd.nextRcvSeq
              THEN TRUE \* TODO
              ELSE chain
         ELSE chain
    ELSE chain

    
\* Handle "PacketAck" datagrams    
HandlePacketAck(chainID, chain, datagrams) ==
    \* get chainID's connection end
    LET connectionEnd == chain.connectionEnd IN
    \* get chainID's channel end
    LET channelEnd == chain.connectionEnd.channelEnd IN
    \* get valid "PacketAck" datagrams
    LET packetRecvDgrs == {dgr \in datagrams : 
                            /\ dgr.type = "PacketAck"
                            /\ dgr.channelID = GetChannelID(chainID)
                            /\ dgr.proofHeight \in chain.counterpartyClientHeights} IN
    
    TRUE \* TODO
    
        
=============================================================================
\* Modification History
\* Last modified Wed Aug 05 12:21:16 CEST 2020 by ilinastoilkovska
\* Created Wed Jul 29 14:30:04 CEST 2020 by ilinastoilkovska
