# IBC packet handling

This document specifies datagram creation logic for packets. It is used by the relayer.

## Data Types

```go
type Packet {
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

```go
type PacketRecv {
     packet          Packet
     proof           CommitmentProof
     proofHeight     Height
}
```

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

```go
type ChannelEnd {
    state                           ChannelState
    ordering                        ChannelOrder
    counterpartyPortIdentifier      Identifier
    counterpartyChannelIdentifier   Identifier
    connectionHops                  [Identifier]
    version                         string
}

enum ChannelState {
  INIT,
  TRYOPEN,
  OPEN,
  CLOSED,
}

enum ChannelOrder {
  ORDERED,
  UNORDERED,
}
```

```go
type ConnectionEnd {
    state                               ConnectionState
    counterpartyConnectionIdentifier    Identifier
    counterpartyPrefix                  CommitmentPrefix
    clientIdentifier                    Identifier
    counterpartyClientIdentifier        Identifier
    version                             []string
}

enum ConnectionState {
  INIT,
  TRYOPEN,
  OPEN,
}
```

```go
type ClientState {
  chainID                       string
  validatorSet                  List<Pair<Address, uint64>>
  trustLevel                    Rational
  trustingPeriod                uint64
  unbondingPeriod               uint64
  latestHeight                  Height
  latestTimestamp               uint64
  frozenHeight                  Maybe<uint64>
  upgradeCommitmentPrefix       CommitmentPrefix
  upgradeKey                    []byte
  maxClockDrift                 uint64
  proofSpecs                    []ProofSpec
}
```

## Computing destination chain

```golang
func getDestinationInfo(ev IBCEvent, chainA Chain) Chain {
    switch ev.type {
        case SendPacketEvent: 
            channel, proof = GetChannel(chainA, ev.sourcePort, ev.sourceChannel, ev.Height)
            if proof == nil return nil
                
            connectionId = channel.connectionHops[0]
            connection, proof = GetConnection(chainA, connectionId, ev.Height) 
            if proof == nil return nil
                
            clientState = GetClientState(chainA, connection.clientIdentifier, ev.Height) 
            return getHostInfo(clientStateA.chainID)     
    }
}
```

## Datagram creation logic

### PacketRecv datagram creation

```golang
func createDatagram(ev SendPacketEvent, chainA Chain, chainB Chain, installedHeight Height) PacketRecv {        
    
    // Stage 1 
    // Verify if packet is committed to chain A
    
    proofHeight = installedHeight - 1
    packetCommitment, packetCommitmentProof = 
        GetPacketCommitment(chainA, ev.sourcePort, ev.sourceChannel, ev.sequence, proofHeight)     
    if packetCommitmentProof != nil { return nil }
        
    // if packet commitment is empty, then packet is already received by the counter party
    if packetCommitment == null OR
    if packetCommitment != hash(concat(ev.data, ev.timeoutHeight, ev.timeoutTimestamp)) { return nil }
            
    // Stage 2 
    // Execute checks IBC handler on chainB will execute
    
    channelB, proof = GetChannel(chainB, ev.destPort, ev.destChannel, LATEST_HEIGHT)
    if proof == nil { return nil }
    
    if channelB == null OR
       channelB.state != OPEN OR
       ev.sourcePort != channelB.counterpartyPortIdentifier OR
       ev.sourceChannel != channelB.counterpartyChannelIdentifier { return nil }
    
    connectionIdB = channelB.connectionHops[0]
    connectionB, proof = GetConnection(chainB, connectionIdB, LATEST_HEIGHT) 
    if proof == nil { return nil }
    
    if connectionB == null OR connectionB.state != OPEN { return nil } 
    
    if ev.timeoutHeight != 0 AND GetConsensusHeight(chainB, LATEST_HEIGHT) >= ev.timeoutHeight { return nil }
    if ev.timeoutTimestamp != 0 AND GetCurrentTimestamp(chainB, LATEST_HEIGHT) >= ev.timeoutTimestamp { return nil }
    
    // we now check if this packet is already received by the destination chain
    if (channel.order === ORDERED) {    
        nextSequenceRecv, proof = GetNextSequenceRecv(chainB, ev.destPort, ev.destChannel, LATEST_HEIGHT) 
        if proof != nil { return nil }
        
        if ev.sequence != nextSequenceRecv { return nil } // packet has already been delivered by another relayer
    
    } else {
        packetAcknowledgement, proof = GetPacketAcknowledgement(ev.destPort, ev.destChannel, ev.sequence)
        if proof != nil { return nil }

        if packetAcknowledgement != nil { return nil }
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
    
    return PacketRecv { packet, packetCommitmentProof, proofHeight }
}    
```


