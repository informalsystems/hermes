# ADR 004: Relayer Domain Decomposition

## Changelog
* 21.7.2020: Initial sketch
* 27.7.2020: Dependencies outline
* 5.10.2020: Update based on sketch
* 2.11.2020: Reviewed & accepted

## Context

The IBC handlers queries and relayer are defined loosely in the [specs].
The goal of this ADR is to provide clarity around the basic domain objects
from the perspective of the relayer,
their interfaces as well as dependencies between them in order to
guide the implementation. The success criteria for the decomposition is
how well it can be tested. It's expected that any decomposition will
lend itself to tight unit tests allowing more collaborators make change
in the code base with confidence.

## Decision
The decomposition should be motivated by what we want to test and what
we need to mock out to exercise the core logic.

We want to be able to test the following high-level functions:

* Client create and update
    * With different chain states
* Connection handshake
    * With different chain states
* Channel Setup
    * With different chain states
* Datagram Construction
    * With different chain states
* Datagram to Transaction
    * Batching
    * Signing
* Datagram Submission
    * With different chain states
    * Missing Client Updates
    * With Missing Proofs
* Handlers (datagrams, chain state) -> events
    * Handling the batch of datagrams 
        * With different chain states
        * Specifically, the key value store
    * Produce events

## Dependencies

In this section, we map the operations which need to be performed at different
stages of both the relayer and the IBC handlers. This gives an outline
of what low-level operations and dependencies need to be mocked out to test each
stage in isolation, and will inform the design of the various traits needed
to mock those out.

Not all stages are listed here because the operations and dependencies
outlined below cover all the possible dependencies at each stage.

### Initializing a connection from the relayer

- Need a relayer configuration (relayer.toml)
- Query chain B for its commitment prefix (ABCI query)
- Send `MsgConnectionOpenInit` message to chain A (transaction)

### `ConnOpenInit` (Handler)

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

For every a transaction in a block of height H:

- call appropriate handler (this is realized by ICS26 routing sub-module),
- If handler succeeds (transaction does not abort), then
  apply the updates to the key-value store (provable & private), and also
  get the current height H and emit appropriate events.

## Objects

The main domain objects in the relayer (`ForeignClient`, `Connection`, `Channel`) 
will be created as concrete types which contain their configuration.
These objects are the relayer's representation of different parts of state from the two chains. 
Dependencies between types indicate runtime dependencies of the chain
state. For instance, objects parameterized by a `ForeignClient` type, such as a `Connection`,
have the pre-condition that the runtime completed client creation before operating with
those objects.

### ChainHandle

The ChainHandle trait is a local representation of a chain state on the relayer.
The API of a ChainHandle provides reliable access to chain state whether
crashed, constructed or queried. We envision a mock version of a chain
will be used to test both handler and relayer logic ([#158]).

The method set of the ChainHandle trait will reflect specific needs and not
intermediate representations. Query and light client verification
concerns will be internal to the chain handle implementation and not exposed
via this API. Users of a ChainHandle implementation (i.e., relayer methods)
can assume verified data or receive an Error and act appropriately.

```rust
trait ChainHandle {
	// Generate a packet
	fn create_packet(&self, event: IBCEvent) -> Result<Packet, ChainError>;

	// Fetch the height of an IBC client hosted by a chain
	// - query the consensus_state of src on dst
	// - query the highest consensus_state
	// - verify if with the light client
	// - return the height
	fn get_height(&self, client: &ForeignClient) -> Result<Height, ChainError>;

	// Submit a transaction to a chains underlying full node
	fn submit(&self, transaction: EncodedTransaction) -> Result<(), ChainError>;

	// ...
}

```

### Connection

```rust
impl Connection {
    fn new(
        chain_a: &ChainHandle,
        chain_b: &ChainHandle, 
        foreign_client_a: &ForeignClient, 
        foreign_client_b: &ForeignClient,
        config: ConnectionConfig)
    -> Result<Connection, Error> {
        // Establish a connection between ChainA and ChainB via ICS 3 handshake.
        // For a first version this can be completely synchronous (a blocking call).
    }
}
```

### Channel 
```rust
impl Channel {
    fn new(
        chain_a: &ChainHandle, 
        chain_b: &ChainHandle, 
        connection: &Connection, 
        config: ChannelConfig) 
    -> Result<Channel, Error> {
        // Establish a channel between two modules (i.e., ICS4 handshake).
    }
}
```

## Link

A link is the object that connects two specific modules on separate chains.
Links are responsible for relaying packets from `chain_a`
to `chain_b` and are therefore uni-directional. A single relayer process 
should be able to support multiple link instances and each link should
run in its own thread. Links depend on `ForeignClient`s,
`Connection` and `Channel`.

```rust
struct Link {
    src_chain: &ChainHandle,
    dst_chain: &ChainHandle,
    channel: &Channel,
}

impl Link {
	fn new(channel: &Channel, config: LinkConfig) 
    -> Link {
		// ...
	}

	/// Relay Link specific packets from src_chain to dst_chain
    /// Expect this to run in a thread
	fn run(self) -> Error {
		let subscription = self.src_chain.subscribe(&self.channel);

		for (target_height, events) in subscription.iter() {
			// ...
            
			let datagrams = events.map(|event| {
				Datagram::Packet(self.dsrc_chain.build_packet(target_height, event))
			});

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
        &dst_chain_handle)?;

    let dst_foreign_client_on_src = ForeignClient::new(
        &src_chain_handle,
        &dst_chain_handle)?;

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

- Accepted (first implementation in [#335](https://github.com/informalsystems/hermes/pull/335)).

## Consequences

### Positive
* Clean abstractions an isolation from IO
* Handshakes are correct by construction
* Sane error handling

### Negative

### Neutral

## References

[specs]: https://github.com/cosmos/ibc/tree/master/spec
[#158]: https://github.com/informalsystems/hermes/issues/158
