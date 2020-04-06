# Understanding the Connection Handshake Protocol

We present three versions of the `connOpenTry` handler:

1. original
2. using new abstraction (Party)
3. using new abstraction + parameter flipping at relayer


### 1. Original

From [ICS 003](https://github.com/cosmos/ics/tree/35e911fa8a9a465a03c73b72b2a3399c15e9ce16/spec/ics-003-connection-semantics):

```typescript
function connOpenTry(
  desiredIdentifier: Identifier,
  counterpartyConnectionIdentifier: Identifier,
  counterpartyPrefix: CommitmentPrefix,
  counterpartyClientIdentifier: Identifier,
  clientIdentifier: Identifier,
  counterpartyVersions: string[],
  proofInit: CommitmentProof,
  proofConsensus: CommitmentProof,
  proofHeight: uint64,
  consensusHeight: uint64) {
    abortTransactionUnless(validateConnectionIdentifier(desiredIdentifier))
    abortTransactionUnless(consensusHeight <= getCurrentHeight())
    expectedConsensusState = getConsensusState(consensusHeight)
    expected = ConnectionEnd{INIT, desiredIdentifier, getCommitmentPrefix(), counterpartyClientIdentifier,
                             clientIdentifier, counterpartyVersions}
    version = pickVersion(counterpartyVersions)
    connection = ConnectionEnd{state, counterpartyConnectionIdentifier, counterpartyPrefix,
                               clientIdentifier, counterpartyClientIdentifier, version}
    abortTransactionUnless(connection.verifyConnectionState(proofHeight, proofInit, counterpartyConnectionIdentifier, expected))
    abortTransactionUnless(connection.verifyClientConsensusState(
      proofHeight, proofConsensus, counterpartyClientIdentifier, consensusHeight, expectedConsensusState))
    previous = provableStore.get(connectionPath(desiredIdentifier))
    abortTransactionUnless(
      (previous === null) ||
      (previous.state === INIT &&
        previous.counterpartyConnectionIdentifier === counterpartyConnectionIdentifier &&
        previous.counterpartyPrefix === counterpartyPrefix &&
        previous.clientIdentifier === clientIdentifier &&
        previous.counterpartyClientIdentifier === counterpartyClientIdentifier &&
        previous.version === version))
    identifier = desiredIdentifier
    state = TRYOPEN
    provableStore.set(connectionPath(identifier), connection)
    addConnectionToClient(clientIdentifier, identifier)
}
```


### 2. Using abstractions

We will use the following three abstractions to parametrize the `connOpenTry` handler:

- The `Party` type:

```typescript
interface Party {
  connectionIdentifier: Identifier
  clientIdentifier: Identifier
  prefix: CommitmentPrefix
}
```

- A `Connection` type:

```typescript
interface Connection {
  state: ConnectionState
  localParty: Party
  remoteParty: Party
  version: string | []string
}
```

- and a `Proof` type:

```typescript
interface Proof {
  content: CommitmentProof,
  height: uint64,
}
```

##### New Handler (version 2)

Now we redefine `connOpenTry` handler as follows:

```typescript
function connOpenTry(
  e: Connection,
  proofInit: Proof,
  proofConsensus: Proof) {
    abortTransactionUnless(validateConnectionIdentifier(e.remoteParty.connectionIdentifier))
    abortTransactionUnless(proofConsensus.height <= getCurrentHeight())
    expectedConsensusState = getConsensusState(proofConsensus.height)

    // basic validation of connection parties
    abortTransactionUnless(e.state === INIT)
    abortTransactionUnless(e.remoteParty.prefix === getCommitmentPrefix())

    abortTransactionUnless(e.remoteParty.verifyConnectionState(proofInit, e))
    abortTransactionUnless(e.remoteParty.verifyClientConsensusState(
      proofConsensus, proofConsensus.height, expectedConsensusState))
    previous = provableStore.get(connectionPath(e.remoteParty.connectionIdentifier))
    abortTransactionUnless(
      (previous === null) ||
      (previous === e))
    identifier = e.remoteParty.connectionIdentifier
    state = TRYOPEN
    provableStore.set(connectionPath(identifier), connection)
    addConnectionToClient(e.remoteParty.clientIdentifier, identifier)
}
```

Notice that this handler accesses predominantly the `remoteParty` fields. This happens because the relayer does not perform any "flipping" of parameters, so the perspective on this object is the one of the counterparty module. This can make it difficult to reason about, so below we discuss a version with flipping.

### 3. Abstraction + flipping

In this version, the relayer performs parameter flipping.
By flipping we mean the reversal of the order of parameters, which the relayer does as follows (this snippet would be placed in [pendingDatagrams](https://github.com/cosmos/ics/tree/master/spec/ics-018-relayer-algorithms)):

```typescript
counterpartyDatagrams.push(ConnOpenTry{
        Connection{ // create a new Connection object
          connection.localParty: originalConnection.remoteParty,
          connection.remoteParty: originalConnection.localParty,
          ...
        }
      })
```

Notice that fields that are called `local` become `remote`, so the perspective on the Connection flips.


##### New Handler definition (Version 3)

With parameter flipping, the `connOpenTry` handler would look more intuitive:

```typescript
function connOpenTry(
  e: Connection,
  proofInit: Proof,
  proofConsensus: Proof) {
    abortTransactionUnless(validateConnectionIdentifier(e.localParty.connectionIdentifier))
    abortTransactionUnless(proofConsensus.height <= getCurrentHeight())
    expectedConsensusState = getConsensusState(proofConsensus.height)

    // basic validation of connection parties
    abortTransactionUnless(e.state === INIT)
    abortTransactionUnless(e.localParty.prefix === getCommitmentPrefix())

    abortTransactionUnless(e.localParty.verifyConnectionState(proofInit, e))
    abortTransactionUnless(e.localParty.verifyClientConsensusState(
      proofConsensus, proofConsensus.height, expectedConsensusState))
    previous = provableStore.get(connectionPath(e.localParty.connectionIdentifier))
    abortTransactionUnless(
      (previous === null) ||
      (previous === e))
    identifier = e.localParty.connectionIdentifier
    state = TRYOPEN
    provableStore.set(connectionPath(identifier), connection)
    addConnectionToClient(e.localParty.clientIdentifier, identifier)
}
```