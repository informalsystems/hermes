# IBC packet handling

This document specifies relayer's logic for packet handling.

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


## Relayer algorithm for packet handling

```golang
func handleSendPacketEvent(ev, chainA) {
    // NOTE: we don't verify if event data are valid at this point. We trust full node we are connected to
    // until some verification fails. Otherwise, we can have Stage 2 (datagram creation being done first).
   
    // Stage 1.
    // Update on `chainB` the IBC client for `chainA` to height `>= targetHeight`.
    targetHeight = ev.height + 1
    // See the code for `updateIBCClient` below.
    
    installedHeight, error := updateIBCClient(chainB, chainA, targetHeight)
    if error != nil {
       return error
    }

    // Stage 2.
    // Create the IBC datagrams including `ev` & verify them.
    
    channel = GetChannel(chainA, ev.sourcePort, ev.sourceChannel) // might query chainA or have this info in state
    connectionId = sourceChannel.connectionHops[0]
    connection = GetConnection(chainA, connectionId) // might query chainA or have this info in state
    clientState = GetClientState(chainA, connection.clientIdentifier) // might query chainA or have this info in state
    chainB = getHostInfo(clientState.chainID)
    
    sh = chainA.lc.get_header(installedHeight)
    
    // we now query for packet data to try to build PacketRecv based on packet data 
    // read at height installedHeight - 1
    
    // is packet for sequence number ev.sequence still pending?
    // we first check if commitment proof is present and valid
    
    provableStore.set(nextSequenceSendPath(packet.sourcePort, packet.sourceChannel), nextSequenceSend)
        provableStore.set(packetCommitmentPath(packet.sourcePort, packet.sourceChannel, packet.sequence),
                          hash(packet.data, packet.timeoutHeight, packet.timeoutTimestamp))
    
    // We query chainA for packetCommitment
    proofHeight = installedHeight - 1
    packetCommitment, proof = GetPacketCommitment(chainA, ev.sourcePort, ev.sourceChannel, ev.sequence, proofHeight)     
    TODO: check what this function is doing!
    if !verifyPacketData(connection,
          proofHeight,
          proof,
          ev.sourcePort,
          ev.sourceChannel,
          ev.sequence,
          concat(ev.data, ev.timeoutHeight, ev.timeoutTimestamp)
        ) {
        panic // full node we are talking to is faulty
    }
    // if packet commitment is empty, then packet is already received by the counter party
    if packetCommitment == null return
    if packetCommitment != hash(ev.data, ev.timeoutHeight, ev.timeoutTimestamp {
        panic  // invalid data; probably fork
    }

    // we now check if this packet is already received by the destination chain
    if (channel.order === ORDERED) {
          // TODO: All get call should either return from the relayer state, or if needed
          // query full node of the chain. In the latter case, proof verification should be done 
          // in the call.     
          nextSequenceRecv = GetNextSequenceRecv(chainB, ev.destPort, ev.destChannel) 
          if ev.sequence != nextSequenceRecv return // packet has already been delivered by another relayer
    } else {
        packetAcknowledgement = GetPacketAcknowledgement(ev.destPort, ev.destChannel, ev.sequence)
        if packetAcknowledgement != null return
    }
    
    packetData = Packet{logEntry.sequence, logEntry.timeoutHeight, logEntry.timeoutTimestamp,
    localEnd.portIdentifier, localEnd.channelIdentifier,
    remoteEnd.portIdentifier, remoteEnd.channelIdentifier, logEntry.data}
    
    
    
    while (true) { 
        datagrams = createDatagram(installedHeight - 1, chainA, chainB)
        if verifyProof(datagrams, sh.appHash) {
            break;  
        }
        // Full node for `chainA` is faulty. Connect to different node of `chainA` and retry.
        replaceFullNode(src)        
     }
    
    // Stage 3.
    // Submit datagrams.
    chainB.submit(datagrams)
}


// Perform an update on `dest` chain for the IBC client for `src` chain.
//    Preconditions:
//      - `src` chain has height greater or equal to `targetHeight`
//    Postconditions:
//      - returns the installedHeight >= targetHeight
//      - return error if verification of client state fails
func updateIBCClient(dest, src, targetHeight) -> {installedHeight, error} {
    
    while (true) { 
        // Check if targetHeight exists already on destination chain.
        // Query state of IBC client for `src` on chain `dest`.
        clientState, membershipProof = dest.queryClientConsensusState(src, targetHeight)    
        // NOTE: What if a full node we are connected to send us stale (but correct) information regarding targetHeight?
        
        // Verify the result of the query
        sh = dest.lc.get_header(membershipProof.Height + 1)
        // NOTE: Headers we obtain from the light client are trusted. 
        if verifyClientStateProof(clientState, membershipProof, sh.appHash) {
            break;
        }
        replaceFullNode(dst)        
    }
    
    // At this point we know that clientState is indeed part of the state on dest chain.              
    // Verify if installed header is equal to the header obtained the from the local client 
    // at the same height.  
    if !src.lc.get_header(clientState.Height) == clientState.SignedHeader.Header {
        // We know at this point that conflicting header is installed at the dst chain.
        // We need to create proof of fork and submit it to src chain and to dst chain so light client is frozen.
        src.lc.createAndSubmitProofOfFork(dst, clientState)
        return {nil, error}
    }
               
    while (clientState.Height < targetHeight) {
        // Installed height is smaller than the target height.
        // Do an update to IBC client for `src` on `dest`.
        shs = src.lc.get_minimal_set(clientState.Height, targetHeight)
        // Blocking call. Wait until transaction is committed to the dest chain.
        dest.submit(createUpdateClientDatagrams(shs))
    
        while (true) { 
            // Check if targetHeight exists already on destination chain.
            // Query state of IBC client for `src` on chain `dest`.
            clientState, membershipProof = dest.queryClientConsensusState(src, targetHeight)    
            // NOTE: What if a full node we are connected to send us stale (but correct) information regarding targetHeight?
                
            // Verify the result of the query
            sh = dest.lc.get_header(membershipProof.Height + 1)
            // NOTE: Headers we obtain from the light client are trusted. 
            if verifyClientStateProof(clientState, membershipProof, sh.appHash) {
                break;
            }
            replaceFullNode(dst)        
        }
            
        // At this point we know that clientState is indeed part of the state on dest chain.              
        // Verify if installed header is equal to the header obtained the from the local client 
        // at the same height.  
        if !src.lc.get_header(clientState.Height) == clientState.SignedHeader.Header {
            // We know at this point that conflicting header is installed at the dst chain.
            // We need to create proof of fork and submit it to src chain and to dst chain so light client is frozen.
            src.lc.createAndSubmitProofOfFork(dst, clientState)
            return {nil, error}
        }
    }

    return {clientState.Height, nil}
}

func getDestinationHost(ev SendPacketEvent, chainA Chain) Chain {
    channel = GetChannel(chainA, ev.sourcePort, ev.sourceChannel) // might query chainA or have this info in state
    connectionId = sourceChannel.connectionHops[0]
    connection = GetConnection(chainA, connectionId) // might query chainA or have this info in state
    clientState = GetClientState(chainA, connection.clientIdentifier) // might query chainA or have this info in state
    return getHostInfo(clientState.chainID)     
}
```

// Deal with packets
    // First, scan logs for sent packets and relay all of them
    sentPacketLogs = queryByTopic(height, "sendPacket")
    for (const logEntry of sentPacketLogs) {
      // relay packet with this sequence number
      packetData = Packet{logEntry.sequence, logEntry.timeoutHeight, logEntry.timeoutTimestamp,
                          localEnd.portIdentifier, localEnd.channelIdentifier,
                          remoteEnd.portIdentifier, remoteEnd.channelIdentifier, logEntry.data}
      counterpartyDatagrams.push(PacketRecv{
        packet: packetData,
        proof: packet.proof(),
        proofHeight: height,
      })
    }


function recvPacket(
  packet: OpaquePacket,
  proof: CommitmentProof,
  proofHeight: Height,
  acknowledgement: bytes): Packet {

    channel = provableStore.get(channelPath(packet.destPort, packet.destChannel))
    abortTransactionUnless(channel !== null)
    abortTransactionUnless(channel.state === OPEN)
    abortTransactionUnless(authenticateCapability(channelCapabilityPath(packet.destPort, packet.destChannel), capability))
    abortTransactionUnless(packet.sourcePort === channel.counterpartyPortIdentifier)
    abortTransactionUnless(packet.sourceChannel === channel.counterpartyChannelIdentifier)

    abortTransactionUnless(connection !== null)
    abortTransactionUnless(connection.state === OPEN)

    abortTransactionUnless(packet.timeoutHeight === 0 || getConsensusHeight() < packet.timeoutHeight)
    abortTransactionUnless(packet.timeoutTimestamp === 0 || currentTimestamp() < packet.timeoutTimestamp)

    abortTransactionUnless(connection.verifyPacketData(
      proofHeight,
      proof,
      packet.sourcePort,
      packet.sourceChannel,
      packet.sequence,
      concat(packet.data, packet.timeoutHeight, packet.timeoutTimestamp)
    ))

    // all assertions passed (except sequence check), we can alter state

    // always set the acknowledgement so that it can be verified on the other side
    provableStore.set(
      packetAcknowledgementPath(packet.destPort, packet.destChannel, packet.sequence),
      hash(acknowledgement)
    )

    if (channel.order === ORDERED) {
      nextSequenceRecv = provableStore.get(nextSequenceRecvPath(packet.destPort, packet.destChannel))
      abortTransactionUnless(packet.sequence === nextSequenceRecv)
      nextSequenceRecv = nextSequenceRecv + 1
      provableStore.set(nextSequenceRecvPath(packet.destPort, packet.destChannel), nextSequenceRecv)
    } else
      abortTransactionUnless(provableStore.get(packetAcknowledgementPath(packet.destPort, packet.destChannel, packet.sequence) === null))

    // log that a packet has been received & acknowledged
    emitLogEntry("recvPacket", {sequence: packet.sequence, timeoutHeight: packet.timeoutHeight,
                                timeoutTimestamp: packet.timeoutTimestamp, data: packet.data, acknowledgement})

    // return transparent packet
    return packet
}

