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
    data               []byte	
}
```

```go
type WriteAcknowledgementEvent {
    height             Height
    port               Identifier
    channel            Identifier
    sequence           uint64
    timeoutHeight      Height
    timeoutTimestamp   uint64    
    data               []byte
    acknowledgement    []byte
}
```

## Event handlers 

### SendPacketEvent handler 

Successful handling of *SendPacketEvent* leads to *PacketRecv* datagram creation.

// NOTE: Stateful relayer might keep packet that are not acked in the state so the following logic
// can be a bit simpler.

```golang
func CreateDatagram(ev SendPacketEvent, 
                    chainA Chain,  // source chain
                    chainB Chain,  // destination chain
                    proofHeight Height) (PacketRecv, Error) {        
    
    // Stage 1 
    // Verify if packet is committed to chain A and it is still pending (commitment exists)
    
    packetCommitment, packetCommitmentProof, error = 
        GetPacketCommitment(chainA, ev.sourcePort, ev.sourceChannel, ev.sequence, proofHeight)     
    if error != nil { return (nil, error) }
        
    if packetCommitment == nil OR
       packetCommitment != hash(concat(ev.data, ev.timeoutHeight, ev.timeoutTimestamp)) { 
            // invalid event; bad provider
            return (nil, Error.BADPROVIDER) 
    }
            
    // Stage 2 
    // Execute checks IBC handler on chainB will execute
    
    channel, proof, error = GetChannel(chainB, ev.destPort, ev.destChannel, LATEST_HEIGHT)
    if error != nil { return (nil, error) }
    
    if channel != nil AND
       (channel.state == CLOSED OR
        ev.sourcePort != channel.counterpartyPortIdentifier OR
        ev.sourceChannel != channel.counterpartyChannelIdentifier) { return (nil, Error.DROP) } 
    
    if channel == nil OR channel.state != OPEN  { return (nil, Error.RETRY) } 
    // TODO: Maybe we shouldn't even enter handle loop for packets if the corresponding channel is not open!
           
    connectionId = channel.connectionHops[0]
    connection, proof, error = GetConnection(chainB, connectionId, LATEST_HEIGHT) 
    if error != nil { return (nil, error) }
    
    if connection == nil OR connection.state != OPEN { return (nil, Error.RETRY) } 
    
    if ev.timeoutHeight != 0 AND GetConsensusHeight(chainB) >= ev.timeoutHeight { return (nil, Error.DROP) }
    if ev.timeoutTimestamp != 0 AND GetCurrentTimestamp(chainB) >= ev.timeoutTimestamp { return (nil, Error.DROP) }
    
    // we now check if this packet is already received by the destination chain
    if channel.ordering === ORDERED {    
       nextSequenceRecv, proof, error = GetNextSequenceRecv(chainB, ev.destPort, ev.destChannel, LATEST_HEIGHT) 
       if error != nil { return (nil, error) }
        
       if ev.sequence != nextSequenceRecv { return (nil, Error.DROP) } // packet has already been delivered by another relayer
    
    } else {
        // Note that absence of receipt (packetReceipt == nil) is also proven also and we should be able to verify it. 
        packetReceipt, proof, error = 
            GetPacketReceipt(chainB, ev.destPort, ev.destChannel, ev.sequence, LATEST_HEIGHT)
        if error != nil { return (nil, error) }

        if packetReceipt != nil { return (nil, Error.DROP) } // packet has already been delivered by another relayer
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

### WriteAcknowledgementEvent handler

Successful handling of *WriteAcknowledgementEvent* leads to *PacketAcknowledgement* datagram creation.

```golang
func CreateDatagram(ev WriteAcknowledgementEvent, 
                    chainA Chain,    // source chain
                    chainB Chain,    // destination chain
                    proofHeight Height) (PacketAcknowledgement, Error) {   

    // Stage 1 
    // Verify if acknowledment is committed to chain A and it is still pending
    packetAck, PacketStateProof, error = 
        GetPacketAcknowledgement(chainA, ev.port, ev.channel, ev.sequence, proofHeight) 
    if error != nil { return (nil, error) }
    
    if packetAck == nil OR packetAck != hash(ev.acknowledgement) { 
        // invalid event; bad provider
        return (nil, Error.BADPROVIDER) 
    }

    // Stage 2 
    // Execute checks IBC handler on chainB will execute
    
    // Fetch channelEnd from the chainA to be able to compute port and chain ids on destination chain
    channelA, proof, error = GetChannel(chainA, ev.port, ev.channel, ev.height)
    if error != nil { return (nil, error) }
    
    channelB, proof, error = 
        GetChannel(chainB, channelA.counterpartyPortIdentifier, channelA.counterpartyChannelIdentifier, LATEST_HEIGHT)
    if error != nil { return (nil, error) }
    
    if channelB == nil OR channel.state != OPEN  { (nil, Error.DROP) } 
    // Note that we checked implicitly above that counterparty identifiers match each other
               
    connectionId = channelB.connectionHops[0]
    connection, proof, error = GetConnection(chainB, connectionId, LATEST_HEIGHT) 
    if error != nil { return (nil, error) }
        
    if connection == nil OR connection.state != OPEN { return (nil, Error.DROP) }
        
    // verify the packet is sent by chainB and hasn't been cleared out yet
    packetCommitment, packetCommitmentProof, error = 
        GetPacketCommitment(chainB, channelA.counterpartyPortIdentifier, 
                            channelA.counterpartyChannelIdentifier, ev.sequence, LATEST_HEIGHT)     
    if error != nil { return (nil, error) }
            
    if packetCommitment == nil OR
       packetCommitment != hash(concat(ev.data, ev.timeoutHeight, ev.timeoutTimestamp)) { 
            // invalid event; bad provider
            return (nil, Error.BADPROVIDER) 
    }
    
    // abort transaction unless acknowledgement is processed in order
    if channelB.ordering === ORDERED {
        nextSequenceAck, proof, error = 
            GetNextSequenceAck(chainB, channelA.counterpartyPortIdentifier, 
                               channelA.counterpartyChannelIdentifier, ev.sequence, LATEST_HEIGHT)  
        if error != nil { return (nil, error) }                                                  

        if ev.sequence != nextSequenceAck { return (nil, Error.DROP) }       
    }
    
    // Stage 3
    // Build datagram as all checks has passed  
    packet = Packet {
                sequence: ev.sequence,
                timeoutHeight: ev.timeoutHeight,
                timeoutTimestamp: ev.timeoutTimestamp,
                sourcePort: channelA.counterpartyPortIdentifier,          
                sourceChannel: channelA.counterpartyChannelIdentifier,
                destPort: ev.port,           
                destChannel: ev.channel,        
                data: ev.data
             }   

    return (PacketAcknowledgement { packet, ev.acknowledgement, PacketStateProof, proofHeight }, nil)
}    
```
