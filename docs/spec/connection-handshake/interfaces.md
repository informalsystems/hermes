# Understanding the Connection Handshake Protocol

We present three versions of the `connOpenTry` handler:

1. original
2. using abstraction (ConnectionEnd)
3. using abstraction + no flipping at relayer

Bonus version:

4. using new abstraction (Party)


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

We will use the following two abstractions to parametrize the `connOpenTry` handler:

- the `ConnectionEnd` interface (cf. ICS 003):

```typescript
interface ConnectionEnd {
  state: ConnectionState
  counterpartyConnectionIdentifier: Identifier
  counterpartyPrefix: CommitmentPrefix
  clientIdentifier: Identifier
  counterpartyClientIdentifier: Identifier
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

##### New Handler version

Now we redefine `connOpenTry` handler:


```typescript
function connOpenTry(
  localConnEnd: ConnectionEnd,
  remoteConnEnd: ConnectionEnd,
  proofInit: Proof,
  proofConsensus: Proof) {
    localConnId := remoteConnEnd.counterpartyConnectionIdentifier
    abortTransactionUnless(validateConnectionIdentifier(localConnId))
    abortTransactionUnless(proofConsensus.height <= getCurrentHeight())
    expectedConsensusState = getConsensusState(proofConsensus.height)

    // basic validation of connection ends
    abortTransactionUnless(remoteConnEnd.state === INIT && localConnEnd.state === INIT)
    abortTransactionUnless(remoteConnEnd.counterpartyPrefix === getCommitmentPrefix())

    // verify the proofs
    abortTransactionUnless(localConnEnd.verifyConnectionState(proofInit,  remoteConnEnd))
    abortTransactionUnless(localConnEnd.verifyClientConsensusState(
      proofConsensus, proofConsensus.height, expectedConsensusState))
    previous = provableStore.get(connectionPath(localConnId))
    abortTransactionUnless(
      (previous === null) ||
      (previous.state === INIT && previous === localConnEnd))
    state = TRYOPEN
    provableStore.set(connectionPath(localConnEnd), connection)
    addConnectionToClient(clientIdentifier, localConnEnd)
}
```

### 3. Abstraction + no flipping

In this version, the relayer does not do any "flipping" of the parameters.
By flipping we mean the reversal of the order of parameters, which the relayer does as follows (this snippet is from [pendingDatagrams](https://github.com/cosmos/ics/tree/master/spec/ics-018-relayer-algorithms)):

```typescript
counterpartyDatagrams.push(ConnOpenTry{
        desiredIdentifier: localEnd.counterpartyConnectionIdentifier,
        counterpartyConnectionIdentifier: localEnd.identifier,
        counterpartyClientIdentifier: localEnd.clientIdentifier,
        ...
      })
```

Notice that fields that are called `local*` become `counterparty*`, so they go from being local to being remote (and vice versa).

If we parametrize the handler to accept `ConnectionEnd` objects (like we do in version 2 above), then the relayer would act as follows:

```typescript
counterpartyDatagrams.push(ConnOpenTry{
        localConnEnd: remoteEnd,
        remoteConnEnd: localEnd
        ...
      })
```
Notice the flipping.


##### New Handler definition (Version 3)

If we avoid flipping of parameters, the relayer would do:

```typescript
counterpartyDatagrams.push(ConnOpenTry{
        localConnEnd: localEnd,
        remoteConnEnd: remoteEnd
        ...
      })
```

Now we redefine `connOpenTry` handler as follows:

```typescript
function connOpenTry(
  remoteConnEnd: ConnectionEnd,
  localConnEnd: ConnectionEnd,
  proofInit: Proof,
  proofConsensus: Proof) {
    // function body is the same as version 2
  }
```
Notice that now call 'remote' what the relayer called 'local' (first parameter of this handler) -- and the other way around.


### 4. Using new abstractions

###### Preliminary declaration:

Let's introduce a `Party` type:

```typescript
interface Party {
  connectionIdentifier: Identifier
  clientIdentifier: Identifier
  prefix: CommitmentPrefix
}
```

A `Connection` type:

```typescript
interface Connection {
  state: ConnectionState
  localParty: Party
  remoteParty: Party
  version: string | []string
}
```

The `Proof` type is the same as above.


##### New Handler definition (Version 4)

**FIX: this needs more thinkering.**

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