# ADR 011: Light client crates extraction

## Changelog

* 2022-07-29: Initial draft

## Context

The current design of the `ibc` (modules) crate precludes light client implementations from being hosted outside of the
ibc-rs repository. This is primarily due to circular dependencies and tight coupling between the light client
implementations and the `ibc` crate.

For e.g., the Tendermint light client implementation (rightly) depends on the `ibc` crate for the trait definitions
(such as `ClientState`) that a light client is expected to implement, but the `ibc` crate also depends on the Tendermint
light client's `ClientState` impl to define its `AnyClientState` enum:

```rust
pub enum AnyClientState {
    Tendermint(client_state::ClientState),

    #[cfg(any(test, feature = "mocks"))]
    Mock(MockClientState),
}
```

See [ADR003 - Dealing with chain-specific datatypes](https://github.com/informalsystems/ibc-rs/blob/master/docs/architecture/adr-003-handler-implementation.md#dealing-with-chain-specific-datatypes)
for the rationale behind the `Any*` enum design choice.

Additionally, there are places where the core modules code (indirectly) depends on light client specific types. e.g.:

```rust
pub fn from_tx_response_event(height: Height, event: &tendermint::abci::Event) -> Option<IbcEvent> {
    if let Some(mut client_res) = ClientEvents::try_from_tx(event) {
        client_res.set_height(height);
        Some(client_res)
    }
    /* ... */
}
```

As we look to add support for more light-clients, it would be much desirable for the core modules code to be
light client agnostic allowing light client implementations to be hosted externally, and, maintained & audited
independently.

It would be possible to break the circular dependencies by extracting all core code (types, traits, etc.) that a
light client implementation would possibly need into a separate crate, say `ibc-base`, and then have both the `ibc`
modules crate and light client implementation crates depend on that `ibc-base` crate. This was implemented in PR
[#2327](https://github.com/informalsystems/ibc-rs/pull/2327), but the solution seems to be fragile and unmaintainable.

This ADR proposes to break the circular dependency problem by removing the `Any*` enums completely and using
trait-objects in their place.

## Decision

### Object safety

There are a total of 5 light client traits, each associated with an `Any*` enum that implements it ->

* `AnyClient` implements `ClientDef`.
* `AnyClientState` implements `ClientState`.
* `AnyConsensusState` implements `ConsensusState`.
* `AnyHeader` implements `Header`.
* `AnyMisbehaviour` implements `Misbehaviour`.

In order to replace the `Any*` enums with trait objects, these light client traits must be object safe. This
essentially means that these traits cannot have a `Self: Sized` requirement and their methods cannot have type
parameters & cannot use `Self`. These restrictions, their implications and possible workarounds are documented below.

#### Traits that require `Self: Sized` cannot be used as supertraits

Common traits that the light client traits depend on that have the `Self: Sized` requirement
are `core::convert::{Into<T>, From<T>, ...}`, `tendermint_proto::Protobuf`, `Clone`, etc.

An easy workaround is to add these methods directly to the trait, for e.g. we add an `encode_vec()` method to
the `Header` trait directly.

```rust
pub trait ClientState {
    /// Encode to canonical binary representation
    fn encode_vec(&self) -> Vec<u8>;

    /* ... */
}
/// instead of ->
/// pub trait ClientState: Protobuf<Any> { /* ... */}
```

#### `Clone` cannot be a supertrait and cannot be derived for types containing boxed trait objects

The following can be made to work using the `dyn-clone` crate ->

```rust
#[derive(Clone)]
pub struct Result {
    pub client_id: ClientId,
    pub client_state: Box<dyn ClientState>,
    pub consensus_state: Box<dyn ConsensusState>,
}
```

```rust
pub trait ClientState: dyn_clone::DynClone { /* ... */ }

dyn_clone::clone_trait_object!(ClientState);
```

`dyn-clone` also provides a `clone_box()` function that can be used to get a `Box<T>` from a `&T`.

#### Deriving `serde::{Serialize, Deserialize}` for trait objects

Replacing the `AnyHeader` with a `Box<dyn Header>` wouldn't work in the code below because `Deserialize`
requires `Self: Sized` and `Serialize` uses generic types.

```rust
#[derive(Deserialize, Serialize)]
pub struct UpdateClient {
    pub common: Attributes,
    pub header: Option<AnyHeader>,
}
```

This can be solved using the `ibc_proto::google::protobuf::Any` type instead and having the light client traits provide
an encoding to `Any` ->

```rust
use ibc_proto::google::protobuf::Any;

pub trait Header {
    /// Encode to canonical protobuf representation
    fn encode_any(&self) -> Any;

    /* ... */
}
```

Thankfully, the core modules code doesn't use the `serde` derivations except in logs and errors. Host and light-client
implementations can optionally choose to downcast to the concrete type and use it's `serde` derivations directly (if
available).

#### Light client traits cannot have constructors

This restriction comes from the fact that trait methods of object safe traits cannot return `Self`.  
However, we would need a ctor to be able to create a `ClientState` and `ConsensusState` in the `create_client` handler.
This can be done using a `where Self: Sized` clause on the trait method.

```rust
use ibc_proto::google::protobuf::Any;

pub trait ClientState {
    fn decode(any: Any) -> Box<dyn ClientState> where Self: Sized;

    /* ... */
}
```

## Status

Proposed

## Consequences

### Positive

* Light client implementations can be hosted in separate crates outside the ibc-rs repo.
* Light client implementations can be maintained & audited independently. clearer ownership
* The `ibc` crate would be light client agnostic and wouldn't need to be updated to add support for newer light clients.
* Host chain implementations will be able to choose the light clients they wish to support.
* Facilitates separation of client-specific code.

### Negative

* Restrictions due to object safety - associated types cannot be used, supertraits cannot have `Sized` as supertrait,
  cannot derive common traits (such as `Copy`, `serde::{Serialize, Deserialize}`, etc.) on types containing trait
  objects, etc.
* Possible performance hit due to heap allocations and dynamic dispatch.

### Neutral

* Client registry must be maintained and kept up-to-date, although host implementations are not forced to rely on the
  registry to add support for light clients that are not in the registry.

## References

* PRs for removing `Any*` enums:
    * Remove all occurences of Any* enums from light clients
      ([PR #2332](https://github.com/informalsystems/ibc-rs/pull/2332))
    * Remove Any* enums ([PR #2338](https://github.com/informalsystems/ibc-rs/pull/2338))
* Experimental PR for extracting `ibc-base` crate ([PR #2327](https://github.com/informalsystems/ibc-rs/pull/2327))
* Rationale behind design choice for `Any*` enums
  ([ADR003: Dealing with chain-specific datatypes](https://github.com/informalsystems/ibc-rs/blob/master/docs/architecture/adr-003-handler-implementation.md#dealing-with-chain-specific-datatypes))

