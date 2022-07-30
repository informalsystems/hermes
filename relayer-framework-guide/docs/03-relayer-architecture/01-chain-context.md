# Chain Context

```rust
trait Async: Sized + Send + Sync + 'static {}
```

```rust
# trait Async: Sized + Send + Sync + 'static {}
#
trait ErrorContext: Async {
    type Error: Async;
}
```

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

```rust
# trait Async: Sized + Send + Sync + 'static {}
#
# trait ErrorContext: Async {
#     type Error: Async;
# }
#
# trait Message {
#     type Signer;
#     type RawMessage;
#     type EncodeError;
#
#     fn encode_raw(&self, signer: &Self::Signer) ->
#       Result<Self::RawMessage, Self::EncodeError>;
#
#     fn estimate_len(&self) -> Result<usize, Self::EncodeError>;
# }
#
trait ChainContext: ErrorContext {
    type Height: Async;

    type Timestamp: Async;

    type Message: Async + Message;

    type Event: Async;
}
```
