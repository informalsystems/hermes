# ADR 001: Repository Structure

## Changelog

* 2020-07-22: First draft.

## Context

This repository comprises a Rust implementation of the [IBC](https://github.com/cosmos/ics) suite of protocols.
To complement this implementation, this repository also comprises specifications, primarily written in TLA+, and
sometimes in English.

At the moment we are invested mostly in the development of a relayer and several important modules (client, connection,
channel, and packets).
Eventually, we hope to cover the full IBC suite.

## Decision

The structure of the `ibc-rs` repository comprises three broad parts:

1. The codebase for the IBC relayer implementation in Rust is in `relayer\`, which consists of crates `relayer-cli` (the
frontend application of the relayer) as well as crate `relayer` (the core relayer functionality).
2. The codebase for IBC modules is in `modules\`, making up the crate called `relayer-modules`.
3. English and TLA+ specs reside under `docs/spec`, classified by the component they target, e.g., relayer or connection
handshake.

Following the work in [#142](https://github.com/informalsystems/ibc-rs/issues/142), the crate
[ibc-proto](https://docs.rs/ibc-proto/) (originally in a [separate repo](https://github.com/informalsystems/ibc-proto))
shall also become absorbed into the present repo. 

#### Crate `relayer-cli`

The basic concern of this crate is to provide user-facing functionality for the IBC relayer. This means
implementing a CLI application that dispatches a _command_ to a specific part of the relayer and then outputs the result
of executing that command. The CLI functionality builds on
[Abscissa](https://docs.rs/abscissa_core/0.5.2/abscissa_core/).

This crate can fulfil various commands, e.g. `query` a chain for some specific part of their store, `start` the relayer,
or start the `light` client for a given chain. For the first few releases these commands provide incomplete
functionality.
 

#### Crate `relayer`

#### Crate `relayer-modules`



#### Crate `ibc_proto`

The `ibc-proto` library gives a developer access to the Cosmos SDK IBC proto-defined structs directly in Rust.
The canonical IBC structs reside presently in [cosmos-sdk](https://github.com/cosmos/cosmos-sdk/tree/master/proto/ibc),
defined in a proto3 syntax.
We compile these structs via prost directly to .rs files and import them into the other crates typically under the same
name prefixed with "Raw", for example:

```Rust
use ibc_proto::channel::Channel as RawChannel;
```

For any Raw data type that is defined in `ibc-proto` we implement the `TryFromRaw` trait, which serves as a translation
& validation layer between the proto ("Raw") types and the domain types. For example, for a `Channel` we do as follows:

```Rust
impl TryFromRaw for ChannelEnd {
    type RawType = RawChannel;
    type Error = anomaly::Error<Kind>;

    fn try_from(value: RawChannel) -> Result<Self, Self::Error> {
        // Translate, validate each field from RawChannel into a Channel.
    }
```

This issue [#130](https://github.com/informalsystems/ibc-rs/issues/130) is a good starting place for more context
on `ibc-proto`.

### References

The following resources serve as reference implementations or specifications that we use to guide the development of
the present crates:

For the IBC relayer:

- A first implementation of the IBC relayer in Golang is under active development at
[iqlusioninc/relayer](https://github.com/iqlusioninc/relayer).
- The English specification of the relayer algorithm is captured in the
[ICS018](https://github.com/cosmos/ics/tree/master/spec/ics-018-relayer-algorithms) spec.

For IBC modules:

- A Golang implementation of IBC modules is under active development as part of the Cosmos SDK,
at [cosmos/cosmos-sdk/x/ibc](https://github.com/cosmos/cosmos-sdk/tree/master/x/ibc).
- The English specifications for IBC modules reside in [cosmos/ics](https://github.com/cosmos/ics/tree/master/spec).

## Status

Proposed

## Consequences

Not applicable.