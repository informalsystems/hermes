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

The rationale behind the `Any*` enum design choice is described
in [ADR003 - Dealing with chain-specific datatypes](https://github.com/informalsystems/ibc-rs/blob/master/docs/architecture/adr-003-handler-implementation.md#dealing-with-chain-specific-datatypes)
->
> We could alternatively model all chain-specific datatypes as boxed trait objects (`Box<dyn Trait>`), but this approach
> runs into a lot of limitations of trait objects, such as the inability to easily require such trait objects to be
> Clonable, or Serializable, or to define an equality relation on them. Some support for such functionality can be found
> in third-party libraries, but the overall experience for the developer is too subpar.
>
> We thus settle on a different strategy: lifting chain-specific data into an enum over all possible chain types.

Additionally, there are places where the core modules code (indirectly) depends on light client specific types. For
e.g., in the code below, the `ClientEvents::try_from_tx()` function must be able to deserialize a light client specific
header from the `UpdateClient` event.

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
parameters & cannot use `Self`. These restrictions, their implications, and possible workarounds are documented below.

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
However, we would need a constructor to be able to create a `ClientState` and `ConsensusState` in the `create_client`
handler. This can be done using a `where Self: Sized` clause on the trait method.

```rust
use ibc_proto::google::protobuf::Any;

pub trait ClientState {
    fn decode(any: Any) -> Box<dyn ClientState> where Self: Sized;

    /* ... */
}
```

### Downcasting support

We need the ability to upcast `&dyn T` to `&dyn core::any::Any` to be able to downcast to a concrete type. This can be
done using a trait with a blanket implementation ->

```rust
pub mod dynamic_typing {
    use core::any::Any;

    pub trait AsAny: Any {
        fn as_any(&self) -> &dyn Any;
    }

    impl<T: Any> AsAny for T {
        fn as_any(&self) -> &dyn Any {
            self
        }
    }
}
```

All light client traits could then add `AsAny` as a supertrait.

```rust
use crate::dynamic_typing::AsAny;

pub trait Header: AsAny { /* ... */ }
```

And usage would look like ->

```rust
fn downcast_header(h: &dyn Header) -> Result<&TmHeader, Ics02Error> {
    h.as_any()
        .downcast_ref::<TmHeader>()
        .ok_or_else(|| Ics02Error::client_args_type_mismatch(ClientType::Tendermint))
}
```

### Special case: removing `AnyClient`

The `AnyClient` enum is special as it is mostly stateless and always created on-the-fly (using `ClientType`) during
verification in the handlers. e.g. `update_client::process()` ->

```rust
pub fn process(
    ctx: &dyn ClientReader,
    /* ... */
) -> HandlerResult<ClientResult, Error> {
    /* ... */

    let client_type = ctx.client_type(&client_id)?;

    let client_def = AnyClient::from_client_type(client_type);

    /* ... */
}
```

This is problematic because it means the module code must be aware of a `ClientType` -> `ClientDef` mapping. This can be
solved by requiring the `ClientReader` trait to provide us with its `ClientDef` implementation.

```rust
pub trait ClientReader {
    /// Return the `ClientDef` implementation for the client with specified `ClientId`
    fn client_def(&self, client_id: &ClientId) -> Box<dyn ClientDef>;

    /* ... */
}
```

Now, we can use the `ClientReader` to get the `ClientDef` implementation for a particular `ClientId` ->

```rust
pub fn process(
    ctx: &dyn ClientReader,
    /* ... */
) -> HandlerResult<ClientResult, Error> {
    /* ... */

    let client_def = ctx.client_def(&client_id);

    /* ... */
}
```

### Domain types containing light client specific types

Raw types such as `MessageCreateClient` contain light client `ClientState` and `ConsensusState` serialized
as `google::protobuf::Any`.

```rust
pub struct MsgCreateClient {
    /// light client state
    #[prost(message, optional, tag = "1")]
    pub client_state: ::core::option::Option<super::super::super::super::google::protobuf::Any>,
    /// consensus state associated with the client that corresponds to a given
    /// height.
    #[prost(message, optional, tag = "2")]
    pub consensus_state: ::core::option::Option<super::super::super::super::google::protobuf::Any>,
    /* ... */
}
```

Ideally, the domain type would contain validated `ClientState` and `ConsensusState` types but this is not possible
anymore because the `ibc` crate cannot depend on the light client crates. It is therefore proposed that domain types
continue to use the `Any` type for such fields and defer the validation to the handlers.

### Light client specific code

A sizeable amount of light client specific code exists in the `ibc` crate today that is only used by `hermes`.
For e.g. helper functions that extract `IbcEvent`s from `tendermint::abci::Event`s (i.e. `from_tx_response_event()`).
It should be fairly straightforward to move such code into the `ibc-relayer` crate.

There are cases where core types depend on light client types, for e.g. `ics02_client::Error`
uses `ics07_tendermint::Error`s in some of its variants ->

```rust
use crate::clients::ics07_tendermint::error::Error as Ics07Error;

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        /* ... */
    
        Tendermint
            [ Ics07Error ]
            | _ | { "tendermint error" },

        TendermintHandlerError
            [ Ics07Error ]
            | _ | { format_args!("Tendermint-specific handler error") },

        /* ... */
    }
}
```

A `ClientSpecific` variant can be provided as a workaround with an accompanying `From<Ics07Error>` impl (for ease of
use) ->

```rust
// modules/src/core/ics02_client/error.rs
define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        /* ... */
    
        ClientSpecific
            { description: String }
            | e | { format_args!("client specific error: {0}", e.description) },
    
        /* ... */
    }
}
```

```rust
// modules/src/clients/ics07_tendermint/error.rs
impl From<Ics07Error> for Ics02Error {
    fn from(e: Ics07Error) -> Self {
        Self::client_specific(e.to_string())
    }
}
```

Additionally, some of that code might be helpful for host implementations, for e.g. event conversions from `IbcEvent`
to `tendermint::abci::Event` are required for `deliverTx` implementation. Note that code such as this does not lead to
the circular dependency problem that this ADR attempts to address and therefore can continue to live in the `ibc` crate;
although ideally it should not.

It is recommended that most client specific code is moved either to the `ibc-relayer` crate or the light client crates
and issues of this kind be dealt with on a case-by-case basis.

### Light client registry

With the proposals in this ADR, the `ibc` crate would be light client agnostic, however, the host implementation must
still be aware of all light clients that it wishes to support. For e.g., after an upgrade a blockchain must be able to
deserialize types from the persistent store.
Furthermore, protobuf has emerged as the canonical serialization scheme for IBC, and IBC's message definitions usually
serialize light client types using the `google::protobuf::Any` type where the `type_url` is accepted to uniquely
represent specific light client types, although this has not been standardized yet.
It is proposed to standardize this and provide a `ibc-client-registry` crate which standardizes this and collects all
known light client implementations. This crate must provide one deserialization entry-point function per light client
type ->

```rust
use ibc_proto::google::protobuf::Any;

pub const TENDERMINT_HEADER_TYPE_URL: &str = "/ibc.lightclients.tendermint.v1.Header";

fn decode_header(any_header: Any) -> Result<Box<dyn Header>, Error> {
    match any_header.type_url {
        TENDERMINT_HEADER_TYPE_URL => TendermintHeader::try_from(any_header).map_err(|e| Error::decode_header(e)),
        /* ... */
        _ => Err(Error::unsupported_client())
    }
}
```

This way we have a standardized list of supported light clients so that host implementations would not have to directly
import every single light client crate that they wish to support. The crate could feature gate light client support to
provide hosts with a more granular control of which light clients they wish to support.

The crate must come with a disclaimer that inclusion in the registry does not imply any guarantees on the correctness of
the light client implementations themselves.

Note that host implementations will be able to add support for light clients regardless of whether they are included in
the registry.

### Splitting the work across multiple PRs

It is suggested that the proposed changes be split across multiple PRs in the following way ->

* Remove `Any*` enums usage from light client implementations and make the light client traits object safe.
* Move tendermint specific code out of the `ibc` crate and into either the `ibc-relayer` crate or the light client
  implementation.
* Remove all `Any*` enums from the `ibc` crate. Pin other workspace crates to stable `ibc` version.
* Extract the light client implementations into separate crates.
* Update all workspace crates to use new API.

A long-lived branch may be used to not block development on the modules code in the meantime.

## Status

Proposed

## Consequences

### Positive

* Light client implementations can be hosted in separate crates outside the ibc-rs repo.
* Light client implementations can be maintained & audited independently, resulting in clearer ownership.
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

