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
light client agnostic allowing light client implementations to be hosted externally, and, maintained and audited
independently.

It would be possible to break the circular dependencies by extracting all core code (types, traits, etc.) that a
light client implementation would possibly need into a separate crate, say `ibc-base`, and then have both the `ibc`
modules crate and light client implementation crates depend on that `ibc-base` crate. This was implemented in PR
[#2327](https://github.com/informalsystems/ibc-rs/pull/2327), but the solution seems to be fragile and unmaintainable.

This ADR proposes to remove the `Any*` enums completely and use trait-objects in their place.

## Decision



### Object safety




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
  cannot derive common traits on types with trait objects, etc.
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

