# ADR 012: Handlers validation and execution separation

## Status
Proposed

## Changelog
* 9/9/2022: initial proposal

## Context

The main purpose of this ADR is to split each IBC handler (e.g. `UpdateClient`, `ConnOpenTry`, etc.) into a "validation" and an "execution" phase in order to accomodate a larger class of host architectures such as Namada. We call "validation" the part of a handler that does all the checks necessary for correctness. We call "execution" the part of the handler that applies the state modifications, assuming that validation passed. 

Our current `deliver()` entrypoint can then be split into 2 entrypoints: `validate()` and `execute()`. More specifically, we replace the current `Ics26Context` and all its supertraits with 2 traits: `ValidationContext` and `ExecutionContext`. `ValidationContext` exposes and implements the `validate()` entrypoint, while the `ExecutionContext` exposes and implements the `execute()` entrypoint. Note that we will still expose `deliver()` (perhaps slightly modified) for convenience.

This ADR will only concern itself with the external-facing API.

The following are out of scope for this ADR:
+ Exposing an `async` API
+ Enabling light clients to define and require the host to implement a set of traits


## Decision

### Validation vs Execution
Each handler can be split into validation and execution. *Validation* is the set of statements which can make the transaction fail. It comprises all the "checks". Execution is the set of statements which mutate the state. In the IBC standard handlers, validation occurs before execution. Note that execution can fail in practice, if say a write operation fails.

As an example, consider the [`UpdateClient` handler](https://github.com/cosmos/ibc/blob/main/spec/core/ics-002-client-semantics/README.md#update).

```javascript
function updateClient(
  id: Identifier,
  clientMessage: ClientMessage) {
    // Validation START
    clientState = provableStore.get(clientStatePath(id))
    abortTransactionUnless(clientState !== null)

    clientState.VerifyClientMessage(clientMessage)
    // Validation END
    
    // Execution START
    foundMisbehaviour := clientState.CheckForMisbehaviour(clientMessage)
    if foundMisbehaviour {
        clientState.UpdateStateOnMisbehaviour(clientMessage)
    }
    else {    
        clientState.UpdateState(clientMessage) 
    }
    // Execution END
}
```

### `ValidationContext` and `ExecutionContext`
Below, we define the `ValidationContext` and `ExecutionContext`.

```rust
trait ValidationContext {
    /// Validation entrypoint.
    fn validate(&self, message: Any) -> Result<(), Error> {
        /* implemented by us */
    }

    /* See Appendix A for a full method list */
}
```

```rust
trait ExecutionContext {
    /// Execution entrypoint
    fn execute(&mut self, message: Any) -> Result<(), Error> {
        /* implemented by us */
    }

    /* See Appendix A for a full method list */
}
```

A useful way to understand how these traits work together is in seeing how *they could* be used to implement `deliver()`.

```rust
fn deliver<V, E>(val_ctx: &V, exec_ctx: &mut E, message: Any) -> Result<(), Error> {
    // NOT how we will actually implement `deliver()`
    let _ = val_ctx.validate(message)?;
    exec_ctx.execute(message)
}
```
Note however that we will not implement `deliver()` this way for efficiency reasons (see [discussion](https://github.com/informalsystems/ibc-rs/issues/2582#issuecomment-1229988512)).

### Host based API

ICS24 defines the minimal set of interfaces which must be provided by an IBC enabled blockchain. We therefore define a
`Host` trait that formalizes and encapsulates these interfaces.

```rust
pub trait Host {
    /// An error type that can represent all host errors.
    type Error;

    /// The Host's key-value store that must provide access to IBC paths. 
    type KvStore: IbcStore<Self::Error>;

    /// An event logging facility.
    type EventLogger: EventLogger<Event=Event<DefaultIbcTypes>>;

    /// Methods to access the store (ro & rw). 
    fn store(&self) -> &Self::KvStore;
    fn store_mut(&mut self) -> &mut Self::KvStore;

    /// Methods to access the event logger (ro & rw).
    fn event_emitter(&self) -> &Self::EventLogger;
    fn event_emitter_mut(&mut self) -> &mut Self::EventLogger;

    /// Host system data (that is not required to be stored on the KV store)
    fn current_timestamp(&self) -> IbcTimestamp;
    fn current_height(&self) -> IbcHeight;

    /* Other methods that cannot be derived from the Store... */
}
```

See the Appendix B below for an exhaustive list of all `Host` methods.

We will provide blanket implementations for `ValidationContext` and `ExecutionContext` for any type which implements `Host`.

```rust
impl<H: Host> ValidationContext for H { /* ... */ }
impl<H: Host> ExecutionContext for H { /* ... */ }
```

#### Event logging

Hosts are expected to provide an implementation of the `EventLogger` trait that provides an event logging facility for
the handlers.

```rust
pub trait EventLogger: Into<Vec<Self::Event>> {
    /// Event type
    type Event;

    /// Return the events emitted so far in the block
    fn events(&self) -> &[Self::Event];

    /// Emit an event
    fn emit_event(&mut self, event: Self::Event);
}
```

#### Store

Hosts are expected to provide an implementation of the `IbcStore` trait that provides access to all IBC paths as defined
by `ibc::core::ics24_host::path::Path`.

```rust
pub trait IbcStore<Error>:
TypedStore<ClientTypePath, ClientType, Error=Error>
+ TypedStore<ClientStatePath, Box<dyn ClientState>, Error=Error>
+ TypedStore<ClientConsensusStatePath, Box<dyn ConsensusState>, Error=Error>
/* ... */
{}
```

Note that we will provide a blanket implementation of `IbcStore` for all types that implement all the `TypedStore`s declared in the `IbcStore` supertraits.

The generic `TypedStore` trait is defined as follows.

```rust
pub trait TypedStore<K, V> {
    type Error;

    fn set(&mut self, key: K, value: V) -> Result<(), Self::Error>;

    fn get(&self, key: K) -> Result<Option<V>, Self::Error>;

    fn delete(&mut self, key: K) -> Result<(), Self::Error>;
}
```

Hosts may choose to implement the `TypedStore` trait individually for every IBC path-value combination or generically as a blanket implementation.

##### Note: Path to value type mapping

We will also provide a pairing of IBC paths to their respective value types. This will make it easier for hosts to implement their generic `TypedStore` using these trait bounds.

```rust
pub trait ValueTypeAtStorePath: private::Sealed {
    type ValueType;
}

impl ValueTypeAtStorePath for ClientTypePath {
    type ValueType = IbcClientType;
}

impl ValueTypeAtStorePath for ClientStatePath {
    type ValueType = Box<dyn ClientState>;
}

impl ValueTypeAtStorePath for ClientConsensusStatePath {
    type ValueType = Box<dyn ConsensusState>;
}

/* ... */
```

See appendix C for an example of how we intend this to be used.


## Consequences

### Positive
+ Architectures that run "validation" separately from "execution" will now be able to use the handlers

### Negative
+ Still no async support
+ Light clients still cannot specify new requirements on the host `Context`

### Neutral

## References

* [Issue #2582: ADR for redesigning the modules' API](https://github.com/informalsystems/ibc-rs/issues/2582)
* [ICS24 spec](https://github.com/cosmos/ibc/blob/1b73c158dcd3b08c6af3917618dce259e30bc21b/spec/core/ics-024-host-requirements/README.md)

## Appendices

### Appendix A: Full `ValidationContext` and `ExecutionContext`

```rust
trait ValidationContext {
    /// Validation entrypoint.
    fn validate(&self, message: Any) -> Result<(), Error> {
        /* implemented by us */
    }

    /// Returns the ClientState for the given identifier `client_id`.
    fn client_state(&self, client_id: &ClientId) -> Result<Box<dyn ClientState>, Error>;

    /// Tries to decode the given `client_state` into a concrete light client state.
    fn decode_client_state(&self, client_state: Any) -> Result<Box<dyn ClientState>, Error>;

    /// Retrieve the consensus state for the given client ID at the specified
    /// height.
    ///
    /// Returns an error if no such state exists.
    fn consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<Box<dyn ConsensusState>, Error>;

        /// Search for the lowest consensus state higher than `height`.
    fn next_consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<Option<Box<dyn ConsensusState>>, Error>;

    /// Search for the highest consensus state lower than `height`.
    fn prev_consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<Option<Box<dyn ConsensusState>>, Error>;

    /// Returns the current height of the local chain.
    fn host_height(&self) -> Height;

    /// Returns the current timestamp of the local chain.
    fn host_timestamp(&self) -> Timestamp {
        let pending_consensus_state = self
            .pending_host_consensus_state()
            .expect("host must have pending consensus state");
        pending_consensus_state.timestamp()
    }

    /// Returns the `ConsensusState` of the host (local) chain at a specific height.
    fn host_consensus_state(&self, height: Height) -> Result<Box<dyn ConsensusState>, Error>;

    /// Returns a natural number, counting how many clients have been created thus far.
    /// The value of this counter should increase only via method `ClientKeeper::increase_client_counter`.
    fn client_counter(&self) -> Result<u64, Error>;

    /// Returns the ConnectionEnd for the given identifier `conn_id`.
    fn connection_end(&self, conn_id: &ConnectionId) -> Result<ConnectionEnd, Error>;

    /// Returns the oldest height available on the local chain.
    fn host_oldest_height(&self) -> Height;

    /// Returns the prefix that the local chain uses in the KV store.
    fn commitment_prefix(&self) -> CommitmentPrefix;

    /// Returns a counter on how many connections have been created thus far.
    fn connection_counter(&self) -> Result<u64, Error>;

        /// Function required by ICS 03. Returns the list of all possible versions that the connection
    /// handshake protocol supports.
    fn get_compatible_versions(&self) -> Vec<Version> {
        get_compatible_versions()
    }

    /// Function required by ICS 03. Returns one version out of the supplied list of versions, which the
    /// connection handshake protocol prefers.
    fn pick_version(
        &self,
        supported_versions: Vec<Version>,
        counterparty_candidate_versions: Vec<Version>,
    ) -> Result<Version, Error> {
        pick_version(supported_versions, counterparty_candidate_versions)
    }

    /// Returns the ChannelEnd for the given `port_id` and `chan_id`.
    fn channel_end(&self, port_channel_id: &(PortId, ChannelId)) -> Result<ChannelEnd, Error>;

    fn connection_channels(&self, cid: &ConnectionId) -> Result<Vec<(PortId, ChannelId)>, Error>;

    fn get_next_sequence_send(
        &self,
        port_channel_id: &(PortId, ChannelId),
    ) -> Result<Sequence, Error>;

    fn get_next_sequence_recv(
        &self,
        port_channel_id: &(PortId, ChannelId),
    ) -> Result<Sequence, Error>;

    fn get_next_sequence_ack(
        &self,
        port_channel_id: &(PortId, ChannelId),
    ) -> Result<Sequence, Error>;

    fn get_packet_commitment(
        &self,
        key: &(PortId, ChannelId, Sequence),
    ) -> Result<PacketCommitment, Error>;

    fn get_packet_receipt(&self, key: &(PortId, ChannelId, Sequence)) -> Result<Receipt, Error>;

    fn get_packet_acknowledgement(
        &self,
        key: &(PortId, ChannelId, Sequence),
    ) -> Result<AcknowledgementCommitment, Error>;

    /// Compute the commitment for a packet.
    /// Note that the absence of `timeout_height` is treated as
    /// `{revision_number: 0, revision_height: 0}` to be consistent with ibc-go,
    /// where this value is used to mean "no timeout height":
    /// <https://github.com/cosmos/ibc-go/blob/04791984b3d6c83f704c4f058e6ca0038d155d91/modules/core/04-channel/keeper/packet.go#L206>
    fn packet_commitment(
        &self,
        packet_data: Vec<u8>,
        timeout_height: TimeoutHeight,
        timeout_timestamp: Timestamp,
    ) -> PacketCommitment {
        let mut hash_input = timeout_timestamp.nanoseconds().to_be_bytes().to_vec();

        let revision_number = timeout_height.commitment_revision_number().to_be_bytes();
        hash_input.append(&mut revision_number.to_vec());

        let revision_height = timeout_height.commitment_revision_height().to_be_bytes();
        hash_input.append(&mut revision_height.to_vec());

        let packet_data_hash = self.hash(packet_data);
        hash_input.append(&mut packet_data_hash.to_vec());

        self.hash(hash_input).into()
    }

    fn ack_commitment(&self, ack: Acknowledgement) -> AcknowledgementCommitment {
        self.hash(ack.into()).into()
    }

    /// A hashing function for packet commitments
    fn hash(&self, value: Vec<u8>) -> Vec<u8>;

    /// Returns the time when the client state for the given [`ClientId`] was updated with a header for the given [`Height`]
    fn client_update_time(&self, client_id: &ClientId, height: Height) -> Result<Timestamp, Error>;

    /// Returns the height when the client state for the given [`ClientId`] was updated with a header for the given [`Height`]
    fn client_update_height(&self, client_id: &ClientId, height: Height) -> Result<Height, Error>;

    /// Returns a counter on the number of channel ids have been created thus far.
    /// The value of this counter should increase only via method
    /// `ChannelKeeper::increase_channel_counter`.
    fn channel_counter(&self) -> Result<u64, Error>;

    /// Calculates the block delay period using the connection's delay period and the maximum
    /// expected time per block.
    fn block_delay(&self, delay_period_time: Duration) -> u64 {
        calculate_block_delay(delay_period_time, self.max_expected_time_per_block())
    }

}
```

```rust
trait ExecutionContext {
    /// Execution entrypoint
    fn execute(&mut self, message: Any) -> Result<(), Error> {
        /* implemented by us */
    }

    /// Called upon successful client creation
    fn store_client_type(
        &mut self,
        client_type_path: ClientTypePath,
        client_type: ClientType,
    ) -> Result<(), Error>;

    /// Called upon successful client creation and update
    fn store_client_state(
        &mut self,
        client_state_path: ClientStatePath,
        client_state: Box<dyn ClientState>,
    ) -> Result<(), Error>;

    /// Called upon successful client creation and update
    fn store_consensus_state(
        &mut self,
        consensus_state_path: ClientConsensusStatePath,
        consensus_state: Box<dyn ConsensusState>,
    ) -> Result<(), Error>;

    /// Called upon client creation.
    /// Increases the counter which keeps track of how many clients have been created.
    /// Should never fail.
    fn increase_client_counter(&mut self);

    /// Called upon successful client update.
    /// Implementations are expected to use this to record the specified time as the time at which
    /// this update (or header) was processed.
    fn store_update_time(
        &mut self,
        client_id: ClientId,
        height: Height,
        timestamp: Timestamp,
    ) -> Result<(), Error>;

    /// Called upon successful client update.
    /// Implementations are expected to use this to record the specified height as the height at
    /// at which this update (or header) was processed.
    fn store_update_height(
        &mut self,
        client_id: ClientId,
        height: Height,
        host_height: Height,
    ) -> Result<(), Error>;

    /// Stores the given connection_end at path
    fn store_connection(
        &mut self,
        connections_path: ConnectionsPath,
        connection_end: &ConnectionEnd,
    ) -> Result<(), Error>;

    /// Stores the given connection_id at a path associated with the client_id.
    fn store_connection_to_client(
        &mut self,
        client_connections_path: ClientConnectionsPath,
        client_id: &ClientId,
    ) -> Result<(), Error>;

    /// Called upon connection identifier creation (Init or Try process).
    /// Increases the counter which keeps track of how many connections have been created.
    /// Should never fail.
    fn increase_connection_counter(&mut self);

    fn store_packet_commitment(
        &mut self,
        commitments_path: CommitmentsPath,
        commitment: PacketCommitment,
    ) -> Result<(), Error>;

    fn delete_packet_commitment(&mut self, key: CommitmentsPath)
        -> Result<(), Error>;

    fn store_packet_receipt(
        &mut self,
        path: ReceiptsPath,
        receipt: Receipt,
    ) -> Result<(), Error>;

    fn store_packet_acknowledgement(
        &mut self,
        key: (PortId, ChannelId, Sequence),
        ack_commitment: AcknowledgementCommitment,
    ) -> Result<(), Error>;

    fn delete_packet_acknowledgement(
        &mut self,
        key: (PortId, ChannelId, Sequence),
    ) -> Result<(), Error>;

    fn store_connection_channels(
        &mut self,
        conn_id: ConnectionId,
        port_channel_id: &(PortId, ChannelId),
    ) -> Result<(), Error>;

    /// Stores the given channel_end at a path associated with the port_id and channel_id.
    fn store_channel(
        &mut self,
        port_channel_id: (PortId, ChannelId),
        channel_end: &ChannelEnd,
    ) -> Result<(), Error>;

    fn store_next_sequence_send(
        &mut self,
        port_channel_id: (PortId, ChannelId),
        seq: Sequence,
    ) -> Result<(), Error>;

    fn store_next_sequence_recv(
        &mut self,
        port_channel_id: (PortId, ChannelId),
        seq: Sequence,
    ) -> Result<(), Error>;

    fn store_next_sequence_ack(
        &mut self,
        port_channel_id: (PortId, ChannelId),
        seq: Sequence,
    ) -> Result<(), Error>;

    /// Called upon channel identifier creation (Init or Try message processing).
    /// Increases the counter which keeps track of how many channels have been created.
    /// Should never fail.
    fn increase_channel_counter(&mut self);

    /// Ibc events
    fn emit_ibc_event(event: IbcEvent);

    ////////////////////////////////////////////////////////
    /* All "read" methods necessary in execution handlers */
    ////////////////////////////////////////////////////////
}
```

### Appendix B: List of `Host` methods that cannot be obtained from the `Store`

Here's an exhaustive list of methods whose implementation cannot be derived from the host's key-value `Store` and
therefore must be part of the `Host` trait.

```rust
pub trait Host {
    /// Methods currently in `ClientReader`
    fn decode_client_state(&self, client_state: Any) -> Result<Box<dyn ClientState>, Error>;
    fn host_height(&self) -> Height;
    fn host_timestamp(&self) -> Timestamp;
    fn host_consensus_state(&self, height: Height) -> Result<Box<dyn ConsensusState>, Error>;
    fn client_counter(&self) -> Result<u64, Error>;

    /// Methods currently in `ClientKeeper`
    fn increase_client_counter(&mut self);
    fn store_update_time(
        &mut self,
        client_id: ClientId,
        height: Height,
        timestamp: Timestamp,
    ) -> Result<(), Error>;
    fn store_update_height(
        &mut self,
        client_id: ClientId,
        height: Height,
        host_height: Height,
    ) -> Result<(), Error>;

    /// Methods currently in `ConnectionReader`
    fn host_oldest_height(&self) -> Height;
    fn commitment_prefix(&self) -> CommitmentPrefix;
    fn connection_counter(&self) -> Result<u64, Error>;

    /// Methods currently in `ConnectionKeeper`
    fn increase_connection_counter(&mut self);

    /// Methods currently in `ChannelReader`
    fn connection_channels(&self, cid: &ConnectionId) -> Result<Vec<(PortId, ChannelId)>, Error>;
    fn hash(&self, value: Vec<u8>) -> Vec<u8>;
    fn client_update_time(&self, client_id: &ClientId, height: Height) -> Result<Timestamp, Error>;
    fn client_update_height(&self, client_id: &ClientId, height: Height) -> Result<Height, Error>;
    fn channel_counter(&self) -> Result<u64, Error>;
    fn max_expected_time_per_block(&self) -> Duration;
    fn block_delay(&self, delay_period_time: Duration) -> u64;

    /// Methods currently in `ChannelKeeper`
    fn increase_channel_counter(&mut self);
}
```

### Appendix C: Example host store implementation

Below is an example host store implementation, where raw bytes are stored.

```rust
struct HostStore(BTreeMap<Path, Vec<u8>>);

impl<K, V> TypedStore<K, V> for HostStore
    where
        K: Into<Path> + ValueTypeAtStorePath<Value=V>,
        V: StoreSerde,
{
    type Error = Ics02Error;

    fn set(&mut self, key: K, value: V) -> Result<(), Self::Error> {
        let key = key.into();
        let value = <<K as ValueTypeAtStorePath>::ValueType as StoreSerde>::serialize(value);
        self.0.insert(key, value).map(|_| ()).unwrap();
        Ok(())
    }

    fn get(&self, key: K) -> Result<Option<V>, Self::Error> {
        let key = key.into();
        Ok(self
            .0
            .get(&key)
            .map(|bytes| <<K as ValueTypeAtStorePath>::ValueType as StoreSerde>::deserialize(bytes)))
    }

    fn delete(&mut self, key: K) -> Result<(), Self::Error> {
        let key = key.into();
        self.0.remove(&key).map(|_| ()).unwrap();
        Ok(())
    }
}

/// Abstracts away the serialization/deserialization scheme used by HostStore
pub trait StoreSerde {
    /// Serialize to canonical binary representation
    fn serialize(self) -> Vec<u8>;

    /// Deserialize from bytes 
    fn deserialize(value: &[u8]) -> Self;
}

/* blanket implementation implements IbcStore for HostStore */
```
