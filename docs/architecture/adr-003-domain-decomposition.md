# ADR 003: Domain Decomposition

## Changelog
* 21.7.2020: Initial sketch
* 27.7.2020: Dependencies outline

## Context

The IBC handlers queries and relayer are defined loosely in the spec.
The goal of this ADR is to provide clarity around the domain objects,
their interfaces as well as dependencies between options in order to
guide the implementation. The success criteria for the decomposition is
how well it can be tested. It's expected that any decomposition will
lend itself to tight unit tests allowing more collaborators make change
in the code base with confidence.

## Decision
The decomposition should be motivated by what we want to tests and what
do we need to mock out to exercise the core logic.

* Connection handshake
    * With different chain states
* Channel Setup
    * With different chain states
* Datagram Construction
    * Local light client state
    * With different chain states
    * With different light client states
* Datagram to Transaction
    * batching
    * Signing
* Datagram Submission
    * With different chain states

* Handlers (datagrams, chain state) -> events
    * batch of datagrams and chain states
        * Specifically, the key value store
    * Produce events

* Operational concerns
    * CLI, embedded

## Dependencies

In this section, we map the operations which need to be performed at different
stages of both the relayer and the IBC handlers. This gives an outline
of what operations and depedencies need to be mocked out to test each
stage in isolation, and will inform the design of the various traits needed
to mock those out.

Not all stages are listed here because the operations and dependencies outlined below cover all the possible dependencies at each stage.

### Initializing a connection from the relayer

- Need a relayer configuration (relayer.toml)
- Query chain B for its commitment prefix (ABCI query)
- Send `MsgConnectionOpenInit` message to chain A (transaction)

### ConnOpenInit (Handler)

- Provable store
- Private store

### `updateIBCClient` (Relayer)

- get latest height from chain A
- get client consensus state from chain B
- get latest header + minimal set from chain A
- verify client state proof
- create and submit datagrams to update B's view of A
- replace full node for B with other full node
- create and submit proof of fork
- wait for UpdateClient event

### `pendingDatagrams` (Relayer)

- get connection objects from chain A
- get connection objects from chain B
- get proof\* that A has a connection in INIT state
- get proof\* that A has a consensus state in a given state
  - \* involves querying the chain + get header/minimal set + verify proof
- build `ConnOpenTry` message

### IBC Module

On a transaction in a block of height H:

- call appropriate Handler
- If handler succeeds (transaction is not aborted),
  get the current height H and emit appropriate events.

## Objects
The main domain object will be implemented as a trait. This will allow
dependencies between objects to be mocked out during testing.

### Chain
The Chain object is a local representation of a foreign chain state.
The API of a Chain provides reliable access to chain state Wether
cashed, constructed or queried.

```rust 
struct ChainState {
    // That represents the data that is stored on chain
    // It's expected that the IBC handlers are producing such a state
    // It's expected the the Chain object and queries are effectively
    // caching such a state
    ...
}

```

The actual chain trait will be implemented by a simple synchronous
version at first and offer a mocked alternative for testing.

```rust
trait Chain {
    // Query and potentially cache consensus_state etc
    fn query_*(&mut self, height: Height, ...) -> Result<..., Error> {
        ...
    }

    // Or maybe we should just provide setters and getters and allow

    // Chains have have embeded local light clients to verify headers
    fn verify(&mut self, header: Header, ...) -> Result<..., Error> {
    }

    // 
    fn submit(&mut self, datagrams: vec<Dataram>) -> Result<..., ...> {
        // We can check if the packet is indeed worth submitting here
        ...
        // We can ensure that the remote client is up to date before submitting
        self.update_remote_client();
        ...
    }

    // Produce a subscription of verified events
    fn subscribe(&mut self, ...) -> Subscription {
        // Create a subscription to events in this chains runtime whith
        // access to the chain such that it can verify packets as they
        // come in
        return Subscription::new(self.clone(), ...);
    }
}
```

### Connection

```rust
trait Connection {
    fn new(chain_a: Chain, chain_b: Chain) -> Result<Connection, Error> {
        // Establish a connection ChainA and ChainB via handshake
        // For a first version this can be completely synchronous
        ...
    }
}
```

### Channel {
```
trait Channel {
    fn new(chain_a: Chain, chain_b: Chain) -> Result<Channel, Error> {
        // Establish a channel between two modules
        ...
    }
}
```

### Relay Algorithm
Let's assume we want to relay packets form `chain_a` to `chain_b`. No
error handling specified here but we can imagine that each synchronous
method call

```rust
let mut chain_a = Chain::new(...);
let mut chain_b = Chain::new(...);
let builder = Builder::new(chain_a.clone(), chain_b.clone());
let mut subscription =  chain_a.subscribe(...);

let connection = Connection::new(chain_a, chain_b);

// Each Path is directional and runs in it's own thread
thread::new(move || {
    while Some(event) = match subscription.next() {
        // We have events, but when are they verified?
        // The subscription will only route events that have been light
        // client verified so we don't event need to worry about it.

        // XXX: Clarify the destinction between pending_datagrams and builder
        // What if some packets on A have not been sent to B
        let pending_packets = chain_a.pending_datagrams(chain_b, event.height);
        // Do we need to setup a channel here?

        // Our builder has it's own references to both queries and can
        // perform all the queries it needs to construct a packet
        let datagrams = builder.new(event); // This might include updates?

        chain_b.submit(datagrams); // or this might include updates?
    }
}
```

## Status

Preliminary sketch

## Consequences

### Positive

### Negative

### Neutral

## References
