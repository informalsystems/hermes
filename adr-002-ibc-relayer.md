# ADR {ADR-NUMBER}: {TITLE}

## Changelog
* {date}: {changelog}

## Definitions
On-chain IBC Client (aka IBC Client) - client code running on chain, typically only the lite client verification (?)
Relayer Light Client - full light client functionality, including connecting to at least one provider (full node), storing and verifying headers, etc.
Source chain (aka A chain) - the chain from which the relayer reads the IBC datagram
Destination chain (aka B chain) - the chain where the realyer submits transactions that include the IBC message.

## Context
A relayer process is an off-chain process responsible for relaying IBC packet data & metadata between two or more chains by scanning their states & submitting transactions. This is because in the IBC architecture, modules are not directly sending messages to each other over networking infrastructure, but instead creating and storing the messages to be retrieved and forwarded by a relayer process. 

This document provides an initial specification of a relayer that interconnects Cosmos-SDK/ Tendermint chains.

The diagram below shows a high level view of the relayer and its interactions with the source and destination chains. The next sections go in more details of the different interactions.

![IBC Relayer Architecture Diagram](assets/IBC_relayer.jpeg).

## Assumptions and Dependencies
This section covers assumption and dependencies about the chains and their IBC implementation (consider only the IBC Cosmos-SDK), functionality required by the relayer that is outside the scope of this document, and their Rust implementations availability.

#### Data Availability
The relayer monitors the chain state to determine when packet forwarding is required. The relayer must be able to retrieve the data within some time bound. This is referred to as **data availability**.

#### Data Legibility
IBC protocol defines the minimal data set that must be made available to relayers for correct operation of the protocol. The relayer expects the data to be legible, i.e. **data should be serialized** according to the IBC specification format; this includes consensus state, client, connection, channel, and packet information, and any auxiliary state structure necessary to construct proofs of inclusion or exclusion of particular key/value pairs in state. 
 - [IBC Specification] protobufs(?), encoding

#### IBC Querier Module
IBC host state machines MUST provide query functions for all data available to realyers. For Cosmos/Tendermint chains this means:
- the IBC modules on chain correctly implement and respond to queries
  - [IBC-Modules-Go] an implementation currently exist in Cosmos-SDK
- the relayer needs the ability to send rpc/http ABCI queries to and receive replies from Tendermint/Cosmos-SDK
  - [[ABCI Rust](https://github.com/tendermint/rust-abci)] - ABCI Rust implementation https://github.com/tendermint/rust-abci
  - [IBC-Host-Module] identifier validation is required (ICS-024)
  - [IBC-Modules-Rust] requires Rust types for all query responses
  - [[Merkle-Proofs-Rust](https://github.com/confio/ics23/tree/master/rust)] (candidate implementation) - all query responses include proofs that need to be included in future transactions and the relayer has to validate them 

#### IBC Messages
The relayer creates transactions that include IBC messages to manage clients, connections and channels, and send application packets to destination chains. These messages must be defined in the IBC Rust implementation [IBC-Modules-Rust].

#### IBC Logging System
IBC packet data & timeouts are not stored directly in the chain state and (as this storage is presumed to be expensive) but are instead committed to with a succinct cryptographic commitment (only the commitment is stored).
As a consequence, IBC requires that a **host state machine MUST provide an event logging system** that logs data in the course of transaction execution. **Logs must be queryable** by relayers to read IBC packet data & timeouts. 

The logging system must provide the following functions:
 - [IBC-Modules-Go] emitLogEntry for emitting log entries called by the state machine during transaction execution:
   - type emitLogEntry = (topic: string , data: []byte) => void
   - example: emitLogEntry("sendPacket", {sequence: packet.sequence , data: packet.data, timeout: packet.timeout})
 - [IBC-Modules-Go] queryByTopic for querying past logs matching a given topic:
   - type queryByTopic = (height: uint64 , topic: string) => Array < []byte >

The packet handling and logging is under development at this point.
Note: RPC `TxSearch/"tx_search"` could be use in the meantime.

#### Keyring 
The relay process must have access to its accounts with tokens on all destination chains, with sufficient balance to pay for transaction fees. Account key information must be stored and managed securely. A keyring implementation is required for CRUD key operations. 
[Keyring-RUST] Investigation in existing Rust implementations is needed. (ex: [hwchen-keyring](https://github.com/hwchen/keyring-rs))

#### Implementation of IBC "routing module"
The default IBC handler uses a receiver call pattern, where modules must individually call the IBC handler in order to bind to
ports, start handshakes, accept handshakes, send and receive packets, etc. While this provides flexibility for modules, it imposes extra work on the part of the relayer processes that now needs to track the state of multiple modules. The IBC specification describes an IBC “routing module” to route packets, and simplify the task of relayers. This routing module accepts external datagrams and calls into the IBC handler to deal with handshakes and packet relay. The routing module keeps a lookup table of modules, which it can use to look up and call a module when a packet is received, so that external relayers need only ever relay packets to the routing module.
[IBC-Routing-Module-Go] Initial version of the relayer assumes that chains implement the "routing module"

#### Batching
The relayer may batch transactions if supported by destination chain and allowed by configuration. In this case the relayer  can bundle multiple datagrams into a single transaction, which causes them to be executed in sequence, and amortise any overhead costs (e.g. signature checks for fee payment).
Initial version of the relayer assumes batching is supported by all chains.

## Relayer Requirements

A correct relayer MUST:

- **[R-config-start]** Read, parse, validate a configuration file upon start and configure itself for the configured chains and paths
- **[R-transport]** Have access to the networking protocols (e.g. TCP/IP, UDP/IP, or QUIC/IP) and physical transport, required to read the state of one blockchain/ machine and submit data to another
- **[R-provider]** Maintain connections to at least one full node per chain
- **[R-query]** Query IBC data on source and destination chains
- **[R-light-client]** Run light clients for source chains and 
- **[R-IBC-client]** create and update IBC clients on destination chains 
- **[R-accounts]** Own accounts on destination chains with sufficient balance to pay for transaction fees
- **[R-transact]** Create, sign and forward IBC datagram transactions
- **[R-relay]** Perform correct relaying of all required messages, according to the IBC sub-protocol constraints
- **[R-restart]** Resume correct functionality after restarts
- **[R-upgrade]** Resume correct functionality after upgrades
- **[R-proofs]** Perform proof verification (as it will be done on the destination chain) and not forward messages where proof verification fails

The relayer MAY:
- **[R-config-cli]** Provide ways to change configuration at runtime
- **[R-bisection]** Perform bisection to optimize transaction costs and computation on destination chains
- **[R-relay-prio]** Filter or order transactions based on some criteria (e.g. in accordance with the fee payment model)

## Implementation
The initial implementation will heavily borrow from the Go relayer implementation that uses a "naive" algorithm for relaying messages. The structure of the configuration file is similar with the one in Go (see [Go-Relayer](https://github.com/cosmos/relayer))

### Configuration
Upon start the relayer reads a configuration file that includes global and per chain parameters. The file format is .toml
The relayer performs initialization based on the content of this file. Below is an example of a configuration file.

```$xslt
# This is an IBC relayer sample configuration
title = "IBC Relayer Config Example"

[global]
timeout = "10s"
strategy = "naive"

[[chains]]
  id = "chain-A"
  rpc-addr = "http://localhost:26657"
  account-prefix = "cosmos"
  key-name = "testkey"
  client-ids = ["clA1", "clA2"]
  gas = 200000
  gas-adjustement = 1.3
  gas-price = "0.025stake"
  trusting-period = "336h"

[[chains]]
  id = "chain-B"
  rpc-addr = "http://localhost:26557"
  account-prefix = "cosmos"
  key-name = "testkey"
  client-ids = ["clB1"]
  gas = 200000
  gas-adjustement = 1.3
  gas-price = "0.025stake"
  trusting-period = "336h"

[[connections]]

[connections.src]
  client-id = "clA1"
  connection-id = "conn1-idA-clA1"
[connections.dest]
  client-id = "clB1"
  connection-id = "conn1-idB-clB1"

[[connections.paths]]
  ports = ["app1-port-A", "app1-port-B"]
  direction = "unidirectional"
[[connections.paths]]
  ports = ["app2-port-A", "app2-port-B"]
  direction = "bidirectional"
```

#### Global
```
[global]
timeout = "10s"
strategy = "naive"
```

Relaying is done periodically and the frequency is dictated by the `timeout` parameter. The `strategy` parameter configures the relayer to run a particular relaying algorithm.

#### Chains 
Chain level information including account and key name, gas information, trusting period, etc. All source and destination chains must be listed here.
```
[[chains]]
  id = "chain-B"
  rpc-addr = "http://localhost:26557"
  account-prefix = "cosmos"
  key-name = "testkey"
  client-ids = ["clB1"]
  gas = 200000
  gas-adjustement = 1.3
  gas-price = "0.025stake"
  trusting-period = "336h"
```

#### Relay Paths 
The realyer can be configured to relay between some application ports, over a number of connections and channels, in unidirectional or bidirectional mode.

```$xslt
[[connections]]

[connections.src]
  client-id = "clA1"
  connection-id = "conn1-idA-clA1"
[connections.dest]
  client-id = "clB1"
  connection-id = "conn1-idB-clB1"

[[connections.paths]]
  ports = ["app1-port-A", "app1-port-B"]
  direction = "unidirectional"
[[connections.paths]]
  ports = ["app2-port-A", "app2-port-B"]
  direction = "bidirectional"
```

### Relayer Commands

`relayer start` starts the relayer with the specified configuration file

`relayer verify config` reads and verifies that the specified configuration file parses correctly

Other commands may be added as required.

_Note: it is expected that the chains can be configured with client, connections and channels. For testing purposes gaia application should be run so access to the gaiacli for IBC related configuration is available_

### Light Client Functionality

After the initialization step light clients are instantiated for the source and destination chains within the relayer. 

In addition IBC clients must be created on the source and destination chains if not already present:
- an IBC client for chain A must be instantiated on chain B for successful A->B relay of IBC packets. The client creation is permissionless and a relayer may create a client if not already present. The IBC client is identified by a clientID.
- in order to detect the existence of an A-client with idA on chain B, the relayer should query the A-client consensus state with client ID idA and verify the chain-id.
Notes: It is possible to create multiple clients for same chain. IBC specification does not provide a security model for attempts at diverting transactions to bogus chains. It is the application responsibility to ensure that the destination chain client is configured correctly (?). Clarification is needed here.

The relayer runs its own lite client for A, retrieves and verifies headers, and once the A-client exists on B, it updates chain B with new headers as required. 

The relayer must pay for all transactions, including the `clientUpdate` and therefore there are incentives for optimizations.
For example, light client implementation of Tendermint supports bisection and the relayer may choose to send skipping headers to A-client on B. 
One possibility is to retrieve the consensus state from the A-client on B, initialize its own light client with that state and then get new headers and trigger UpdateClient messages only when forwarding other IBC datagrams that require client updates. This has the advantage of updating the IBC client with the minimum amount of headers but the disatvantage is that the IBC transactions are delayed while relayer runs bisection.
Alternatively the relayer could continuously download headers and then, when required by new IBC datagrams, simulate the bisection algorithm and send a minimum number of ClientUpdate messages with headers from local store. 

### Basic Relayer Algorithm
Note: This algorithm is adapted from the [relayer algorithm described in IBC Specifigication](https://github.com/cosmos/ics/blame/master/spec/ics-018-relayer-algorithms/README.md#L47) and [Go relayer implementation ](https://github.com/cosmos/relayer/blob/f3a302df9e6e0c28883f5480199d3190821bcc06/relayer/strategies.go#L49.).
It only relays from `src` to `dest`.

The relayer algorithm forwards messages over the `src->dest` paths it has been configured for:

- `relay` is called by the relayer periodically but no more than once per block.

- `pendingDatagrams` calculates the set of all valid datagrams to be relayed from one chain to another based on the state of both chains. 
- `submitDatagram` is a procedure defined per-chain to submit transactions. Datagrams can be submitted individually  or as a single transaction if the chain supports it. This version assumes Tendermint chains and bulks datagrams in single transactions.

```typescript
function relay(C: Set<Chain>, P: Set<Paths>) {
  for (dest in C)
    datagrams = []
    // collect datagrams for dest from all sources
    for (src in C)
      if (dest !== src && P.present(src, dest) {
        datagrams = datagrams.append(pendingDatagrams(src, dest))
      }
    }
    submitDatagram(dest, datagrams)
}
```

### Pending Datagrams

`pendingDatagrams` collates datagrams to be sent from one `src` to `dest`.
The relayer process relays all handshakes that started on `src`, relays all packets that need to be sent from `src` to `dest`, and relays all acknowledgements of packets sent from `dest` to `src`.

```typescript
function pendingDatagrams(src: Chain, dest: Chain): Set<Datagram> {

  // ICS2 : Clients
  // - Determine if IBC client need to be created/ updated on dest
  destDatagrams = clientDatagrams(src, dest)
  if len(destDatagrams) != 0 {
    // Submit these immediately
    return destDatagrams
  }

  // ICS3 : Connections
  // - Determine if any connection handshakes are in progress
  destDatagrams = connectionDatagrams(src, dest)
  if len(destDatagrams) != 0 {
    // Submit these immediately
    return destDatagrams
  }

  // ICS4 : Channels
  // - Determine if any channel handshakes are in progress
  destDatagrams = channelDatagrams(src, dest)
  if len(destDatagrams) != 0 {
    // Submit these immediately
    return destDatagrams
  }

  // ICS7: Packet Messages 
  // - Determine if any packets, acknowledgements, or timeouts need to be relayed
  destDatagrams = packetDatagrams(src, dest, destDatagrams)
  if len(destDatagrams) != 0 {
    // Submit these immediately
    return destDatagrams
  }

  return []
}
```

#### Client Datagrams
```typescript
function clientDatagrams(src: Chain, dest: Chain): Set<Datagram>) {

  // - Determine if IBC client needs to be created/ updated on dest
  srcHeight = src.latestHeight()
  srcHeader = src.latestHeader()

  srcClientOnDest, err = dest.queryClientConsensusState(src)
  if err == noExist {
    msg = ClientCreate({dest, srcHeader})
  } else if srcClientOnDest.height < srcHeight {
    msg = ClientUpdate({dest, srcHeader})
  } else {
    return []
  }
  [].push(msg)
}

```

#### Connection Datagrams
```typescript
function connectionDatagrams(src: Chain, dest: Chain): Set<Datagram> {
  destDatagrams = []
  // get all connections between src and dest
  connections = src.queryConnectionsUsingClient()

  for (srcEnd in connections) {
    destEnd = dest.getConnection(srcEnd.destIdentifier)
    switch {

    case (srcEnd.state === UNINITIALIZED && destEnd.state === UNINITIALIZED):
      // Handshake needs to be started, relay ConnOpenInit to dest
      destDatagrams.push(UpdateClient({dest, src.latestHeader()}
      counterparty = Counterparty{
        ClientID: srcEnd.clientIdentifier,
        ConnectionID: srcEnd.identifier
      }
      destDatagrams.push(ConnOpenInit{
        ConnectionID: destEnd.identifier,
        ClientID: destEnd.clientIdentifier,
        Counterparty: counterparty
       })

    case (srcEnd.state === INIT && destEnd.state === UNINITIALIZED):
      // Handshake has started on src, relay UpdateClient and ConnOpenTry to dest
      destDatagrams.push(UpdateClient({dest, src.latestHeader()}
      destDatagrams.push(ConnOpentTry{
        ...
      })

    case (srcEnd.state === TRYOPEN && destEnd.state === INIT):
      // Handshake has started on dest and ConnOpenTry was received on src, 
      // relay UpdateClient and ConnOpenAck to dest
      destDatagrams.push(UpdateClient({dest, src.latestHeader()}
      destDatagrams.push(ConnOpentAck{
        ...
      })

    case (srcEnd.state === OPEN && destEnd.state === TRYOPEN):
      // Handshake has started on src and ConnOpenTry was received on dest, ConnOpenAck was sent by dest to src, 
      // relay UpdateClient and ConnOpenConfirm to dest
      destDatagrams.push(UpdateClient({dest, src.latestHeader()}_
      destDatagrams.push(ConnOpentConfirm{
        ...
      })
    }
}
```

#### Channel Datagrams
The `channelDatagrams` function is very similar to the `connectionDatagrams` 

```typescript
function channelDatagrams(src: Chain, dest: Chain, srcDatagrams: Set<Datagram>, destDatagrams: Set<Datagram>) {
  destDatagrams = []

  // get all channels between src and dest
  connections = src.queryConnectionsUsingClient()
  channels = src.getChannelsUsingConnections(connections)

  for (srcEnd in channels) {
    destEnd = dest.getChannel(srcEnd.destIdentifier)

    switch {
    case (srcEnd.state === UNINITIALIZED && destEnd.state === UNINITIALIZED):
      // Handshake needs to be started, relay ChanOpenInit to dest
      destDatagrams.push(UpdateClient({dest, src.latestHeader()}
      destDatagrams.push(ChannOpenInit{
        ...
      })

    // similar to the connectionDatagrams function
    ....

    }
}
```

#### Packet Datagrams

```typescript
function packetDatagrams(src: Chain, dest: Chain): Set<Datagram>) {
  connections = src.queryConnectionsUsingClient()
  channels = chain.getChannelsUsingConnections(connections)
  height = src.latestHeight()

  for (srcEnd in channels) {
    destEnd = dest.getChannel(srcEnd.destIdentifier)

    // First, scan logs for sent packets and relay all of them
    sentPacketLogs = src.queryByTopic(height, "sendPacket")
    for (logEntry in sentPacketLogs) {
      // relay packet with this sequence number
      packetData = Packet{logEntry.sequence, logEntry.timeout, srcEnd.portIdentifier, srcEnd.channelIdentifier,
                          destEnd.portIdentifier, destEnd.channelIdentifier, logEntry.data}
      destDatagrams.push(PacketRecv{
        packet: packetData,
        proof: packet.proof(),
        proofHeight: height,
      })
    }

    // Then, scan logs for received packets and relay acknowledgements
    recvPacketLogs = src.queryByTopic(height, "recvPacket")
    for (const logEntry of recvPacketLogs) {
      // relay packet acknowledgement with this sequence number
      packetData = Packet{logEntry.sequence, logEntry.timeout, srcEnd.portIdentifier, srcEnd.channelIdentifier,
                          destEnd.portIdentifier, destEnd.channelIdentifier, logEntry.data}
      destDatagrams.push(PacketAcknowledgement{
        packet: packetData,
        acknowledgement: logEntry.acknowledgement,
        proof: packet.proof(),
        proofHeight: height,
      })
    }
}
```

## Inter-relayer Coordination
Multiple realyers may run in parallel and, while it is expected that they relay over disjoint paths, it could be the case that they may submit same transactions to a destination chain. In this case only the first transaction succeeds while subsequent fail causing loss of fees. Ideally some coordination would be in place to avoid this but this is not adressed here.

## Relayer Restarts and Upgrades

 
## Decision

> This section explains all of the details of the proposed solution, including implementation details.
It should also describe affects / corollary items that may need to be changed as a part of this.
If the proposed change will be large, please also indicate a way to do the change to maximize ease of review.
(e.g. the optimal split of things to do between separate PR's)

## Status

> A decision may be "proposed" if it hasn't been agreed upon yet, or "accepted" once it is agreed upon. If a later ADR changes or reverses a decision, it may be marked as "deprecated" or "superseded" with a reference to its replacement.

{Deprecated|Proposed|Accepted}

## Consequences

> This section describes the consequences, after applying the decision. All consequences should be summarized here, not just the "positive" ones.

### Positive

### Negative

### Neutral

## References

> Are there any relevant PR comments, issues that led up to this, or articles referrenced for why we made the given design choice? If so link them here!

* {reference link}
