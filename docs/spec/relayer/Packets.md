# IBC packet handling

This document specifies datagram creation logic for packets. It is used by the relayer.

## Packet related IBC events

```go
type SendPacketEvent {
    height             Height
    sequence           uint64
    timeoutHeight      Height
    timeoutTimestamp   uint64
    sourcePort         Identifier
    sourceChannel      Identifier
    destPort           Identifier
    destChannel        Identifier
    data               bytes	
}
```

## Datagram creation logic

### PacketRecv datagram creation

```golang
func CreateDatagram(ev SendPacketEvent, 
                    chainA Chain, 
                    chainB Chain, 
                    proofHeight Height) (PacketRecv, Error) {        
    
    // Stage 1 
    // Verify if packet is committed to chain A and it is still pending (commitment exists)
    
    packetCommitment, packetCommitmentProof = 
        GetPacketCommitment(chainA, ev.sourcePort, ev.sourceChannel, ev.sequence, proofHeight)     
    if packetCommitmentProof == nil { return (nil, Error.RETRY) }
        
    if packetCommitment == nil OR
       packetCommitment != hash(concat(ev.data, ev.timeoutHeight, ev.timeoutTimestamp)) { 
            // invalid event; replace provider
            ReplaceProvider(chainA)
            return (nil, Error.DROP) 
    }
            
    // Stage 2 
    // Execute checks IBC handler on chainB will execute
    
    channel, proof = GetChannel(chainB, ev.destPort, ev.destChannel, LATEST_HEIGHT)
    if proof == nil { return (nil, Error.RETRY) }
    
    if channel != nil AND
       (channel.state == CLOSED OR
        ev.sourcePort != channel.counterpartyPortIdentifier OR
        ev.sourceChannel != channel.counterpartyChannelIdentifier) { (nil, Error.DROP) } 
    
    if channel == nil OR channel.state != OPEN  { (nil, Error.RETRY) } 
    // TODO: Maybe we shouldn't even enter handle loop for packets if the corresponding channel is not open!
           
    connectionId = channel.connectionHops[0]
    connection, proof = GetConnection(chainB, connectionId, LATEST_HEIGHT) 
    if proof == nil { return (nil, Error.RETRY) }
    
    if connection == nil OR connection.state != OPEN { return (nil, Error.RETRY) } 
    
    if ev.timeoutHeight != 0 AND GetConsensusHeight(chainB) >= ev.timeoutHeight { return (nil, Error.DROP) }
    if ev.timeoutTimestamp != 0 AND GetCurrentTimestamp(chainB) >= ev.timeoutTimestamp { return (nil, Error.DROP) }
    
    // we now check if this packet is already received by the destination chain
    if (channel.ordering === ORDERED) {    
        nextSequenceRecv, proof = GetNextSequenceRecv(chainB, ev.destPort, ev.destChannel, LATEST_HEIGHT) 
        if proof == nil { return (nil, Error.RETRY) }
        
        if ev.sequence != nextSequenceRecv { return (nil, Error.DROP) } // packet has already been delivered by another relayer
    
    } else {
        // Note that absence of ack (packetAcknowledgment == nil) is also proven also and we should be able to verify it. 
        packetAcknowledgement, proof = 
            GetPacketAcknowledgement(chainB, ev.destPort, ev.destChannel, ev.sequence, LATEST_HEIGHT)
        if proof == nil { return (nil, Error.RETRY) }

        if packetAcknowledgement != nil { return (nil, Error.DROP) } // packet has already been delivered by another relayer
    }
    
    // Stage 3
    // Build datagram as all checks has passed  
    packet = Packet {
                sequence: ev.sequence,
                timeoutHeight: ev.timeoutHeight,
                timeoutTimestamp: ev.timeoutTimestamp,
                sourcePort: ev.sourcePort,          
                sourceChannel: ev.sourceChannel,
                destPort: ev.destPort,           
                destChannel: ev.destChannel,        
                data: ev.data
    }   
    
    return (PacketRecv { packet, packetCommitmentProof, proofHeight }, nil)
}    
```


