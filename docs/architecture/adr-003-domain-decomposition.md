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
The decomposition should be motivated by what we want to test and what
we need to mock out to exercise the core logic.

* Client create and update
    * With different chain states
* Connection handshake
    * With different chain states
* Channel Setup
    * With different chain states
* Datagram Construction
    * With different chain states
* Datagram to Transaction
    * batching
    * Signing
* Datagram Submission
    * With different chain states
    * Missing Client Updates
    * With Missing Proofs

* Handlers (datagrams, chain state) -> events
    * handling the batch of datagrams 
        * With different chain states
        * Specifically, the key value store
    * Produce events

## Dependencies

In this section, we map the operations which need to be performed at different
stages of both the relayer and the IBC handlers. This gives an outline
of what operations and dependencies need to be mocked out to test each
stage in isolation, and will inform the design of the various traits needed
to mock those out.

Not all stages are listed here because the operations and dependencies
outlined below cover all the possible dependencies at each stage.

### Initializing a connection from the relayer

- Need a relayer configuration (relayer.toml)
- Query chain B for its commitment prefix (ABCI query)
- Send `MsgConnectionOpenInit` message to chain A (transaction)

### ConnOpenInit (Handler)

- Provable store
- Private store

### `updateIBCClient` (Relayer)

- get the latest height from chain A (Query)
- get client consensus state from chain B (Query)
- get latest header + minimal set from chain A (Light Client)
- verify client state proof (Prover)
- create and submit datagrams to update B's view of A (Message Builder, Transaction)
- replace full node for B with other full node (PeerList)
- create and submit proof of fork (Fork Evidence Reporter)
- wait for UpdateClient event (Event Subscription)

### `pendingDatagrams` (Relayer)
Builds the datagrams required by the given on-chain states. 
For connection datagrams:
- get connection objects from chain A (Query)
- get connection objects from chain B (Query)
- get proof\* of connection state (e.g. `Init`) from chain A (Query, Prover, Light Client)
- get proof\* of client state and consensus state from chain A (Query, Prover, Light Client)
  - \* involves querying the chain + get header/minimal set + verify proof
- build the next message in the connection handshake, e.g. `ConnOpenTry` (Message Builder)

Channel datagrams are built similarly. Packet datagrams are triggered by events, and they are detailed in the Link section below.

### IBC Module

On a transaction in a block of height H:

- call appropriate Handler
- If handler succeeds (transaction is not aborted),
  get the current height H and emit appropriate events.

## Objects
The main domain objects (ForeignClient, Connection, Channel) will be
created as concrete types which contain their configuration.
Dependencies between types indicate runtime dependencies of the chain
state, ie. objects parameterized by ForeignClient have the pre-condition
that the Client creation has completed at some point in the runtime.

### Chain
The Chain trait is a local representation of a foreign chain state.
The API of a Chain provides reliable access to chain state whether
crashed, constructed or queried. We invision a mock version of this chain
will be used to test both handler and relayer logic.

```rust 
struct ChainData {
    // That represents the data that is stored on chain
    // It's expected that the IBC handlers are producing such a state
    // It's expected the the Chain object and queries are effectively
    // caching such a state
    ...
}

```

The method set of the Chain trait will reflect specific needs and not
intermediate representations. Query and light client verification
concerns will be internal to the chain implementation and not exposed
via API. Users of Chain trait implementations can assume verified data
or receive an Error and act appropriately.

```rust
trait Chain {
	// Generate a packet as the 
	fn create_packet(&self, event: IBCEvent) -> Result<Packet, ChainError>

	// Fetch the height of a foreign client on a chain
	// - query the consensus_state of src on dst
	// - query the highest consensus_state
	// - verify if with the light client
	// - return the height
	fn get_height(&self, client: &ForeignClient) -> Result<Height, ChainError>

	// Submit a transaction to a chains underlying full node
	fn submit(&self, transaction: EncodedTransaction) -> Result<(), ChainError>

	...
}

```

### Connection

```rust
impl Connection {
    fn new(chain_a: ..., chain_b: ..., foreign_client_a: ..., foreign_client_b: ..., config: ...) -> Result<Connection, Error> {
        // Establish a connection ChainA and ChainB via handshake
        // For a first version this can be completely synchronous
        ...
    }
}
```

### Channel 
```rust
impl Channel {
    fn new(chain_a: Chain, chain_b: Chain, connection: ..., config: ...) -> Result<Channel, Error> {
        // Establish a channel between two modules
        ...
    }
}
```

## Link
A link is the entity that connects two specific modules on separate chains. Links are responsible for relaying packets from `chain_a`
to `chain_b` and are therefore oriented.  A single relayer process 
should be able to support multiple link instances and each link should
run in its own thread.  Links require established ForeignClient-s,
Connection and Channel.

```rust
struct Link {
    src_chain: Chain,
    dst_chain: Chain,
    channel: Channel,
}

impl Link {
	fn new(..., channel: Channel, config: Config) -> Link {
		...
	}

	/// Relay Link specific packets from src_chain to dst_chain
    /// Expect this to run in a thread
	fn run(self) -> Error {
		let subscription = self.src_chain.subscribe(&self.channel);

		for (target_height, events) in subscription.iter() {
			...
            
			let datagrams = events.map(|event| {
				Datagram::Packet(self.dsrc_chain.build_packet(target_height, event))
			})

			for attempt in self.config_submission_attempts {
                let current_height = self.dst_chain.get_height(&self.connection.channel.foreign_client)?;
                let signed_headers = self.src_chain.get_minimal_set(current_height, target_height)?;

                let mut attempt_datagrams = datagrams.clone();
                attempt_datagrams.push(Datagram::ClientUpdat(ClientUpdate::new(signed_headers)));
				
                let transaction = Transaction::new(datagram);
                self.dst_chain.submit(transaction.sign().encode())?;
			}

		}
	}
}
```

### Example Main
Example of the initializing of a single link between two chains. Each
chain has its own runtime and exposes a `handle` to communicate with
that runtime from different threads. There are dependencies between
ForeignClients, Connections, Channels and Links which are encoded in the
type system. The construction of them reflects that their corresponding
handshake protocol has completed successfully.

```rust
fn main() -> Result<(), Box<dyn Error>> {
    let src_chain = ChainRuntime::new();
    let dst_chain = ChainRuntime::new();

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

    let src_foreign_client_on_dst = ForeignClient::new(
        &src_chain_handle,
        &dst_chain_handle,
        ForeignClientConfig::default())?;

    let dst_foreign_client_on_src = ForeignClient::new(
        &src_chain_handle,
        &dst_chain_handle,
        ForeignClientConfig::default())?;

    let connection = Connection::new(
        &src_chain_handle,
        &dst_chain_handle,
        dst_foreign_client_on_src,
        src_foreign_client_on_dst,
        ConnectionConfig::default()).unwrap();

    let channel = Channel::new(
        &src_chain_handle,
        &dst_chain_handle,
        connection,
        ChannelConfig::default()).unwrap();

    let link = Link::new(
        src_chain_handle,
        dst_chain_handle,
        channel, 
        LinkConfig::default())?;

    link.run()?;

    Ok(())
}
```

## Status

Implemented [#335](https://github.com/informalsystems/ibc-rs/pull/335).

## Consequences

### Positive
* Clean abstractions an isolation from IO
* Handshakes are correct by construction
* Sane error handling

### Negative

### Neutral

## References
