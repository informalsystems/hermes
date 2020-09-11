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
## Helper functions

We assume the existence of the following helper functions:

```go
// Returns channel end with a commitment proof. If proof != nil, then it is being verified with the corresponding light client.
// Channel end is queried at the given chain at the height proofHeight. If LATEST_HEIGHT is passed as a parameter,
// the query should be for latest height for which proof exists (MAX_HEIGHT - 1).
GetChannel(chain Chain, 
           portId Identifier, 
           channelId Identifier,  
           proofHeight Height) (ChannelEnd, CommitmentProof)
 
// Returns connection end with a commitment proof. If proof != nil, then it is being verified with the corresponding light client.
// Connection end is queried at the given chain at the height proofHeight. If LATEST_HEIGHT is passed as a parameter,
// the query should be for latest height for which proof exists (MAX_HEIGHT - 1).
GetConnection(chain Chain, 
              connectionId Identifier, 
              proofHeight Height) (ConnectionEnd, CommitmentProof)


// Returns client connection with a commitment proof. If proof != nil, then it is being verified with the corresponding light client.
// Client state is queried at the given chain at the height proofHeight. If LATEST_HEIGHT is passed as a parameter,
// the query should be for latest height for which proof exists (MAX_HEIGHT - 1).
GetClientState(chain Chain, 
               clientId Identifier, 
               proofHeight Height) (ClientState, CommitmentProof)

// Returns packet commitment with a commitment proof. If proof != nil, then it is being verified with the corresponding light client.
// Packet commitment is queried at the given chain at the height proofHeight. If LATEST_HEIGHT is passed as a parameter,
// the query should be for latest height for which proof exists (MAX_HEIGHT - 1).
GetPacketCommitment(chain Chain, 
                    portId Identifier, 
                    channelId Identifier, 
                    sequence uint64, 
                    proofHeight Height) (bytes, CommitmentProof)

// Returns next recv sequence number a commitment proof. If proof != nil, then it is being verified with the corresponding 
// light client. It is queried at the given chain at the height proofHeight. If LATEST_HEIGHT is passed as a parameter,
// the query should be for latest height for which proof exists (MAX_HEIGHT - 1).
GetNextSequenceRecv(chain Chain, 
                    portId Identifier, 
                    channelId Identifier,  
                    proofHeight Height) (uint64, CommitmentProof)

// Returns packet acknowledgment with a commitment proof. If proof != nil, then it is being verified with the 
// corresponding light client. Packet acknowledgment is queried at the given chain at the height proofHeight. 
// If LATEST_HEIGHT is passed as a parameter, the query should be for latest height for which proof exists (MAX_HEIGHT - 1).
GetPacketAcknowledgement(chain Chain, 
                         portId Identifier, 
                         channelId Identifier, 
                         sequence uint64, 
                         proofHeight Height) (bytes, CommitmentProof)
 
// Returns estimate of the consensus height on the given chain. 
GetConsensusHeight(chain Chain) Height

// Returns estimate of the current time on the given chain. 
GetCurrentTimestamp(chainB) uint64
 
```

## Computing destination chain

```golang
func GetDestinationInfo(ev IBCEvent, chainA Chain) Chain {
    switch ev.type {
        case SendPacketEvent: 
            channel, proof = GetChannel(chainA, ev.sourcePort, ev.sourceChannel, ev.Height)
            if proof == nil return nil
                
            connectionId = channel.connectionHops[0]
            connection, proof = GetConnection(chainA, connectionId, ev.Height) 
            if proof == nil return nil
                
            clientState = GetClientState(chainA, connection.clientIdentifier, ev.Height) 
            return getHostInfo(clientStateA.chainID) 
        ...    
    }
}
```

## Datagram creation logic

### PacketRecv datagram creation

```golang
func createDatagram(ev SendPacketEvent, chainA Chain, chainB Chain, installedHeight Height) PacketRecv {        
    
    // Stage 1 
    // Verify if packet is committed to chain A and it is still pending (commitment exists)
    
    proofHeight = installedHeight - 1
    packetCommitment, packetCommitmentProof = 
        GetPacketCommitment(chainA, ev.sourcePort, ev.sourceChannel, ev.sequence, proofHeight)     
    if packetCommitmentProof != nil { return nil }
        
    if packetCommitment == null OR
       packetCommitment != hash(concat(ev.data, ev.timeoutHeight, ev.timeoutTimestamp)) { return nil }
            
    // Stage 2 
    // Execute checks IBC handler on chainB will execute
    
    channel, proof = GetChannel(chainB, ev.destPort, ev.destChannel, LATEST_HEIGHT)
    if proof != nil { return nil }
    
    if channel == null OR
       channel.state != OPEN OR
       ev.sourcePort != channel.counterpartyPortIdentifier OR
       ev.sourceChannel != channel.counterpartyChannelIdentifier { return nil }
    
    connectionId = channel.connectionHops[0]
    connection, proof = GetConnection(chainB, connectionId, LATEST_HEIGHT) 
    if proof != nil { return nil }
    
    if connectionB == null OR connectionB.state != OPEN { return nil } 
    
    if ev.timeoutHeight != 0 AND GetConsensusHeight(chainB) >= ev.timeoutHeight { return nil }
    if ev.timeoutTimestamp != 0 AND GetCurrentTimestamp(chainB) >= ev.timeoutTimestamp { return nil }
    
    // we now check if this packet is already received by the destination chain
    if (channel.ordering === ORDERED) {    
        nextSequenceRecv, proof = GetNextSequenceRecv(chainB, ev.destPort, ev.destChannel, LATEST_HEIGHT) 
        if proof != nil { return nil }
        
        if ev.sequence != nextSequenceRecv { return nil } // packet has already been delivered by another relayer
    
    } else {
        packetAcknowledgement, proof = 
            GetPacketAcknowledgement(chainB, ev.destPort, ev.destChannel, ev.sequence, LATEST_HEIGHT)
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


