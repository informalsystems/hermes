# Chain Context

## Async Safety

```rust
trait Async: Sized + Send + Sync + 'static {}
```

## Error Context

```rust
# use ibc_relayer_framework::traits::core::Async;
#
trait ErrorContext: Async {
    type Error: Async;
}
```

## Abstract Message

```rust
trait Message {
    type Signer;
    type RawMessage;
    type EncodeError;

    fn encode_raw(&self, signer: &Self::Signer) ->
        Result<Self::RawMessage, Self::EncodeError>;

    fn estimate_len(&self) -> Result<usize, Self::EncodeError>;
}
```

## Chain Context

```rust
# use ibc_relayer_framework::traits::message::Message;
# use ibc_relayer_framework::traits::core::Async;
# use ibc_relayer_framework::traits::core::ErrorContext;
#
trait ChainContext: ErrorContext {
    type Height: Async;

    type Timestamp: Async;

    type Message: Async + Message;

    type Event: Async;
}
```

## Cosmos Message

```rust
use ibc::signer::Signer;
use ibc_proto::google::protobuf::Any;
use prost::{EncodeError, Message as ProtoMessage};
#
# use ibc_relayer_framework::traits::message::Message;

struct CosmosIbcMessage {
    to_protobuf_fn: Box<dyn Fn(&Signer) ->
        Result<Any, EncodeError> + 'static + Send + Sync>,
}

impl Message for CosmosIbcMessage {
    type Signer = Signer;
    type RawMessage = Any;
    type EncodeError = EncodeError;

    fn encode_raw(&self, signer: &Signer) ->
        Result<Any, EncodeError>
    {
        (self.to_protobuf_fn)(signer)
    }

    fn estimate_len(&self) -> Result<usize, Self::EncodeError> {
        let raw = (self.to_protobuf_fn)(&Signer::dummy())?;
        Ok(raw.encoded_len())
    }
}
```

## Cosmos Chain Context

```rust
use ibc::Height;
use ibc::timestamp::Timestamp;
use tendermint::abci::responses::Event;
#
# use ibc_relayer_cosmos::cosmos::message::CosmosIbcMessage;
# use ibc_relayer_framework::traits::core::Async;
# use ibc_relayer_framework::traits::core::ErrorContext;
# use ibc_relayer_framework::traits::chain_context::ChainContext;
# use ibc_relayer_framework::traits::runtime::context::RuntimeContext;

struct Error { /* ... */ }
struct CosmosRuntimeContext;

struct CosmosChainContext<Handle> {
    handle: Handle,
}

impl ErrorContext for CosmosRuntimeContext {
    type Error = Error;
}

impl<Handle: Async> ErrorContext for CosmosChainContext<Handle> {
    type Error = Error;
}

impl<Handle: Async> RuntimeContext for CosmosChainContext<Handle> {
    type Runtime = CosmosRuntimeContext;

    fn runtime(&self) -> &CosmosRuntimeContext {
        &CosmosRuntimeContext
    }
}

impl<Handle: Async> ChainContext for CosmosChainContext<Handle> {
    type Height = Height;

    type Timestamp = Timestamp;

    type Message = CosmosIbcMessage;

    type Event = Event;
}
```
