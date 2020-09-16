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
// Returns channel end with a commitment proof. 
GetChannel(chain Chain, 
           portId Identifier, 
           channelId Identifier,  
           proofHeight Height) (ChannelEnd, CommitmentProof)
 
// Returns connection end with a commitment proof. 
GetConnection(chain Chain, 
              connectionId Identifier, 
              proofHeight Height) (ConnectionEnd, CommitmentProof)


// Returns client state with a commitment proof. 
GetClientState(chain Chain, 
               clientId Identifier, 
               proofHeight Height) (ClientState, CommitmentProof)

// Returns consensus state with a commitment proof. 
GetConsensusState(chain Chain, 
                  clientId Identifier, 
                  targetHeight Height,
                  proofHeight Height) (ConsensusState, CommitmentProof)


// Returns packet commitment with a commitment proof. 
GetPacketCommitment(chain Chain, 
                    portId Identifier, 
                    channelId Identifier, 
                    sequence uint64, 
                    proofHeight Height) (bytes, CommitmentProof)

// Returns next recv sequence number with a commitment proof. 
GetNextSequenceRecv(chain Chain, 
                    portId Identifier, 
                    channelId Identifier,  
                    proofHeight Height) (uint64, CommitmentProof)

// Returns packet acknowledgment with a commitment proof. 
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

For functions that return proof, if proof != nil, then the returned value is being verified. 
The value is being verified using the header's app hash that is provided by the corresponding light client.

### Error handling

Helper functions listed above assume querying (parts of the) application state using Tendermint RPC. For example,
GetChannel relies on QueryChannel. RPC calls can fail as: 

- no response is received within some timeout (TimeoutError) or
- malformed response is received (SerializationError).

In both cases, error handling logic should be defined by the caller. For example, in the former case, the caller might
retry to send the same request to a same provider (full node), while in the latter case the request might be sent to 
some other provider node. Although these kinds of errors could be due to network infrastructure issues, it is normally
simpler to blame the provider (assume implicitly network is always correct and reliable). Therefore, correct provider
always respond timely with a correct response, while in case of errors we consider the provider node faulty, and then 
we replace it with a different node. 

```go
type Chain {
  chainID      string
  clientID     Identifier
  peerList     List<Pair<Address, uint64>>
  provider     Pair<Address, uint64>
  lc           LightClient   
}
```

We now show the pseudocode for one of those functions:

```go
func GetChannel(chain Chain, 
           portId Identifier, 
           channelId Identifier,  
           proofHeight Height) (ChannelEnd, CommitmentProof) {

    while(true) {
        // Query provable store exposed by the full node of chain. 
        // The path for the channel end is at channelEnds/ports/{portId}/channels/{channelId}".
        // The membership proof returned is read at height proofHeight. 
        channel, proof, error = QueryChannel(chain.provider, portId, channelId, proofHeight) 
        if error != nil {
            // elect a new provider from the peer list
            if !ReplaceProvider(chain) { return (nil, nil) }  // return if fail to elect new provider         
        }
    
        header, error = GetHeader(chain.lc, proofHeight) // get header for height proofHeight using light client
        if error != nil { return (nil, nil) }  // return if light client can't provide header for the given height       

        // verify membership of the channel at path channelEnds/ports/{portId}/channels/{channelId} using 
        // the root hash header.AppHash
        if verifyMembership(header.AppHash, proofHeight, proof, channelPath(portId, channelId), channel) {
            return channel, proof
        } 
        
        // membership check fails; therefore provider is faulty. Try to elect new provider
        if !ReplaceProvider(chain) { return (nil, nil) }  // if fails to elect new provider return
    }
    panic // should never reach this line
}

// Simplified version of logic for electing new provider. In reality it will probably involve opening a connection to 
// a newply elected provider and closing connection with an old provider.
func ReplaceProvider(chain Chain) boolean {
    if chain.peerList.IsEmpty() return false
    chain.provider = Head(chain.peerList)
    chain.peerList = Tail(chain.peerList)
    return true
}
```
If LATEST_HEIGHT is passed as a parameter, the data should be read (and the corresponding proof created) 
at the most recent height. 

## Computing destination chain

```golang
func GetDestinationInfo(ev IBCEvent, chain Chain) Chain {
    switch ev.type {
        case SendPacketEvent: 
            channel, proof = GetChannel(chain, ev.sourcePort, ev.sourceChannel, ev.Height)
            if proof == nil { return nil }
                
            connectionId = channel.connectionHops[0]
            connection, proof = GetConnection(chain, connectionId, ev.Height) 
            if proof == nil { return nil }
                
            clientState, proof = GetClientState(chain, connection.clientIdentifier, ev.Height) 
            if proof == nil { return nil }

            // We assume that the relayer maintains a map of known chainIDs and the corresponding chains. 
            // Note that in a normal case, relayer should be aware of chains between it relays packets        
            return getChain(clientState.chainID) 
        ...    
    }
}
```

## Datagram creation logic

### PacketRecv datagram creation

```golang
func createPacketRecvDatagram(ev SendPacketEvent, chainA Chain, chainB Chain, installedHeight Height) PacketRecv {        
    
    // Stage 1 
    // Verify if packet is committed to chain A and it is still pending (commitment exists)
    
    proofHeight = installedHeight - 1
    packetCommitment, packetCommitmentProof = 
        GetPacketCommitment(chainA, ev.sourcePort, ev.sourceChannel, ev.sequence, proofHeight)     
    if packetCommitmentProof != nil { return nil }
        
    if packetCommitment == nil OR
       packetCommitment != hash(concat(ev.data, ev.timeoutHeight, ev.timeoutTimestamp)) { return nil }
            
    // Stage 2 
    // Execute checks IBC handler on chainB will execute
    
    channel, proof = GetChannel(chainB, ev.destPort, ev.destChannel, LATEST_HEIGHT)
    if proof == nil { return nil }
    
    // TODO: not necessarily fatal error as optimistic packet send might be taking place
    if channel == nil OR
       channel.state != OPEN OR
       ev.sourcePort != channel.counterpartyPortIdentifier OR
       ev.sourceChannel != channel.counterpartyChannelIdentifier { return nil }
    
    connectionId = channel.connectionHops[0]
    connection, proof = GetConnection(chainB, connectionId, LATEST_HEIGHT) 
    if proof == nil { return nil }
    
    if connection == nil OR connection.state != OPEN { return nil } 
    
    if ev.timeoutHeight != 0 AND GetConsensusHeight(chainB) >= ev.timeoutHeight { return nil }
    if ev.timeoutTimestamp != 0 AND GetCurrentTimestamp(chainB) >= ev.timeoutTimestamp { return nil }
    
    // we now check if this packet is already received by the destination chain
    if (channel.ordering === ORDERED) {    
        nextSequenceRecv, proof = GetNextSequenceRecv(chainB, ev.destPort, ev.destChannel, LATEST_HEIGHT) 
        if proof == nil { return nil }
        
        if ev.sequence != nextSequenceRecv { return nil } // packet has already been delivered by another relayer
    
    } else {
        // TODO: Can be proof of absence also and we should be able to verify it. 
        packetAcknowledgement, proof = 
            GetPacketAcknowledgement(chainB, ev.destPort, ev.destChannel, ev.sequence, LATEST_HEIGHT)
        if proof == nil { return nil }

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


