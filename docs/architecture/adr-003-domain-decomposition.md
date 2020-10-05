# ADR 003: Domain Decomposition

## Changelog
* 21.7.2020: Initial sketch
* 27.7.2020: Dependencies outline
* 5.10.2020: Update based on sketch

## Context

The IBC handlers queries and relayer are defined loosely in the spec.
The goal of this ADR is to provide clarity around the domain objects,
their interfaces as well as dependencies between them in order to
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

- get latest height from chain A (Query)
- get client consensus state from chain B (Query)
- get latest header + minimal set from chain A (Light Client)
- verify client state proof (Prover)
- create and submit datagrams to update B's view of A (Message Builder, Transaction)
- replace full node for B with other full node (PeerList)
- create and submit proof of fork (Fork Evidence Reporter)
- wait for UpdateClient event (Event Subscription)

### `pendingDatagrams` (Relayer)

- get connection objects from chain A (Query)
- get connection objects from chain B (Query)
- get proof\* that A has a connection in INIT state (Query, Prover, Light Client)
- get proof\* that A has a consensus state in a given state (Query, Prover, Light Client)
  - \* involves querying the chain + get header/minimal set + verify proof
- build `ConnOpenTry` message (Message Builder)

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
The API of a Chain provides reliable access to chain state wether
cashed, constructed or queried. We invision mock version of this chain
will be used to test both handler and relayer logic.

```rust 
struct Chain {
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
    }
}
```

### Connection

```rust
struct Connection {
    fn new(chain_a: ..., chain_b: ..., foreign_client: ..., config: ...) -> Result<Connection, Error> {
        // Establish a connection ChainA and ChainB via handshake
        // For a first version this can be completely synchronous
        ...
    }
}
```

### Channel 
```rust
struct Channel {
    fn new(chain_a: Chain, chain_b: Chain, connection: ..., config: ...) -> Result<Channel, Error> {
        // Establish a channel between two modules
        ...
    }
}
```

## Link
The entity which connects two specific modules on seperate chains is
called a link. Links are responsible for relaying packets from `chain_a`
to `chain_b` and are therefore oriented.  A single relayer process 
should be able to support multiple link instances and each link should
run in it's own thread.  Links require established ForeignClient,
Connection and Channel.

```rust
struct Link {
    src_chain: Chain,
    dst_chain: Chain,
    foreign_client: ForeignClient,
}

impl Link {
	fn new(..., foreign_client, ForeignClient, channel: Channel, config: Config) -> Link {
		...
	}

	/// Relay Link specific packets from src_chain to dst_chain
    /// Expect this to run in a thread
	fn run(mut self, config: Config) -> Error {
		let subscription = self.src_chain.subscribe(config);

		for datagram in subscription.iter() {
			...
            
            self.foreign_client.update(target_height);

			let header = self.src_chain.get_header(target_height);
			verify_proof(&datagram, &header);

            let transaction = Transaction::new(datagram);
            self.dst_chain.submit(transaction);
		}
	}
}
```

### Example Main
Example of the initalizing on a single link between two chains. Each
chain has it's own runtime and exposes a `handle` to communicate with
that runtime from different threads. There are dependencies between
ForeignClients, Connections, Channels and Links which are encoded in the
type system. The construction of them reflects that their corresponding
handshake protocol was completed successfully.

```rust
fn main() -> Result<(), Box<dyn Error>> {
    let src_chain = ChainRuntime::new(); // TODO: Pass chain config
    let dst_chain = ChainRuntime::new(); // TODO: Pass chain config

    /// chains expose handlers for commuicating with the chain related runtime
    /// which move into their own threads
    let src_chain_handle = src_chain.handle();
    thread::spawn(move || {
        src_chain.run().unwrap();
    });

    let dst_chain_handle = dst_chain.handle();
    thread::spawn(move || {
        // What should we do on return here?
        dst_chain.run().unwrap();
    });

    let foreign_client = ForeignClient::new(
        &src_chain_handle,
        &dst_chain_handle,
        ForeignClientConfig::default())?;

    let connection = Connection::new(
        &src_chain_handle,
        &dst_chain_handle,
        &foreign_client, // Create a semantic dependecy
        ConnectionConfig::default()).unwrap();

    let channel = Channel::new(
        &src_chain_handle,
        &dst_chain_handle,
        connection, // Semantic dependecy
        ChannelConfig::default()).unwrap();

    let link = Link::new(
        src_chain_handle,
        dst_chain_handle,
        foreign_client, // Actual dependecy
        channel,        // Semantic dependecy
        LinkConfig::default())?;

    link.run()?;

    Ok(())
}
```

## Status

Partially implemented in [#162](https://github.com/informalsystems/ibc-rs/pull/162).

## Consequences

### Positive

### Negative

### Neutral

## References
