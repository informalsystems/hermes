# ADR 001: Repository Structure

## Changelog

* 2020-07-22: First draft.

## Context

This document provides a basic rundown of the structure of this repository, plus some plans for its evolution.

This repository comprises a Rust implementation of the [IBC](https://github.com/cosmos/ibc) suite of protocols.
To complement this implementation, this repository also comprises specifications, primarily written in TLA+, and
sometimes in English.

At the moment we are invested mostly in the development of a relayer and several important modules (client, connection,
channel, and packets).
Eventually, we hope to cover the full IBC suite. 

## Decision

The `ibc-rs` repository comprises three broad parts:

1. The codebase for the IBC relayer implementation in Rust is in `relayer/`, which consists of crate **`relayer-cli`** (the
frontend application of the relayer) as well as crate **`relayer`** (the core relayer functionality).
2. The codebase for IBC modules is in `modules/`, making up the crate called **`relayer-modules`**.
3. English and TLA+ specs reside under `docs/spec`, classified by the component they target, e.g., relayer or connection
handshake.

Following the work in [#23](https://github.com/cosmos/ibc-proto-rs/issues/23), the crate
**`ibc-proto`**(originally in a [separate repo](https://github.com/informalsystems/ibc-proto) and [documented here](https://docs.rs/ibc-proto/))
shall also become absorbed into the present repo.

In the following, we discuss the current state and proposed evolution of each of the Rust crates.

#### Crate `relayer-cli`

The basic concern of this crate is to provide user-facing functionality for the IBC relayer. This means
implementing a CLI application that dispatches a _command_ to a specific part of the relayer, and then outputs the
result of executing that command. This crate builds on
[Abscissa](https://docs.rs/abscissa_core/0.5.2/abscissa_core/) to simplify command line parsing, application process
lifecycle, and error handling.

This crate can accept various sub-commands, e.g. `query` a chain for some specific part of their store, `start` the
relayer, or start the `light` client for a given chain. Note that most commands can be further refined with parameters
(for instance, the `query` command can be issued for a `connection` or `channel` or `client`). The bulk of data types
and logic resides in `relayer/cli/commands`, grouped by each specific command.

#### Crate `relayer`

This crate implements the core responsibilities of an IBC relayer. Briefly speaking, there are 3 high-level
requirements on a IBC relayer, in no particular order:

- __R1.__ ability to interface with IBC-enabled chains, with the purpose of reading their state and submitting transactions to
these chains;
- __R2.__ ability to run a light client for IBC-enabled chains, with the purpose of verifying headers and state of these chains;
- __R3.__ implement the IBC relayer algorithms (ICS 018).

Some functionality described above overlaps with functionality of IBC Modules. For instance, some logic
that the relayer implements for handling connection handshakes (in ICS18) overlaps with logic in the IBC module specific
for connections (ICS3). Given this overlap, the `relayer-modules` crate serves as the "ground truth" implementing the
said logic, while the `relayer` crate has a natural dependency on `relayer-modules`.

In addition to the dependency on the IBC Modules, the relayer also depends on the `tendermint-rs` crate. This is
useful in particular for interfacing with the light client implementation from this crate, as well as core data types 
such as `SignedHeader`, `Validator`, or `ValidatorSet`.

[ADR 002](./adr-002-ibc-relayer.md) captures more specific details on the relayer architecture.  

#### Crate `relayer-modules`

The [canonical IBC specification](https://github.com/cosmos/ibc/tree/master/spec/) is modular in the sense of grouping
different components of the specification in modules; for instance, specification _ICS03_ pertains to the abstraction of 
IBC connections and the IBC connection handshake protocol, while _ICS04_ pertains to IBC channels and packets.
We group the code in this crate to reflect the modular separation in the canonical IBC specification.

A few common patterns we employ in this crate are as follows.

###### `msgs.rs`

Many IBC protocols involve the receiving and processing of messages.
The protocols for establishing a connection (ICS03) or a channel (ICS04), for example, comprise
the processing of four different types of messages each.
In particular, the data structures representing these messages for connection handshake are `MsgConnectionOpenInit`,
`MsgConnectionOpenTry`, `MsgConnectionOpenAck`, and `MsgConnectionOpenConfirm`.

The creation and validation of protocol messages for each protocol resides in `msgs.rs` within the respective ICS. 
Each of these messages should implement the trait `pub trait Msg`, ensuring that all messages implement a basic
interface allowing them to be routed correctly (via the IBC routing module and with the help of the `route()` method)
or support basic validation. 

###### Error handling

Each ICS enumerates specific errors that may occur within `icsX_NAME/error.rs`.
The error-handling pattern here build on [thiserror](https://lib.rs/crates/thiserror) and
[anomaly](https://lib.rs/crates/anomaly) for capturing the context of errors plus backtraces (optional).
Generally speaking, an IBC module constructs and propagates errors to the caller by two patterns:

```Rust
return Err(Kind::MissingCounterparty.into())
```

or if a context can be supplied this is preferable:

```rust
return Err(Kind::InvalidConnectionHopsLength
                .context("validate channel")
                .into());
```
where the ICS itself defines `Kind::InvalidConnectionHopsLength` and `Kind::MissingCounterparty`.

###### Deserialization

See the details for the crate `ibc-proto` [below](#crate-ibc-proto).

#### Crate `ibc_proto`

The `ibc-proto` library gives a developer access to the Cosmos SDK IBC proto-defined structs directly in Rust.
The canonical IBC structs reside presently in [cosmos-sdk](https://github.com/cosmos/ibc-go/tree/main/proto/ibc),
defined in a proto3 syntax.
We compile these structs via prost directly to .rs files and import them into the other crates typically under the same
name prefixed with "Raw", for example:

```Rust
use ibc_proto::channel::Channel as RawChannel;
```

For any Raw data type that is defined in `ibc-proto` we implement the `DomainType` trait, which serves as a translation
& validation layer between the proto ("Raw") types and the domain types. For example, for a `Channel` we do as follows:

```Rust
impl DomainType<RawChannel> for ChannelEnd {}

impl TryFrom<RawChannel> for ChannelEnd {
    type Error = anomaly::Error<Kind>;

    fn try_from(value: RawChannel) -> Result<Self, Self::Error> {
        // Translate, validate each field from RawChannel into a Channel.
    }
}

impl From<ChannelEnd> for RawChannel {
    fn from(value: ChannelEnd) -> Self {
        // Translate Channel into a RawChannel
    }
}
```

This issue [#130](https://github.com/informalsystems/hermes/issues/130) is a good starting place for more context
on `ibc-proto`.

### References

The following resources serve as reference implementations or specifications that we use to guide the development of
the present crates:

For the IBC relayer:

- A first implementation of the IBC relayer in Golang is under active development at
[iqlusioninc/relayer](https://github.com/iqlusioninc/relayer).
- The English specification of the relayer algorithm is captured in the
[ICS018](https://github.com/cosmos/ibc/tree/master/spec/relayer/ics-018-relayer-algorithms) spec.

For IBC modules:

- A Golang implementation of IBC modules is under active development
at [cosmos/ibc-go](https://github.com/cosmos/ibc-go/tree/main/modules).
- The English specifications for IBC modules reside in [cosmos/ibc](https://github.com/cosmos/ibc/tree/master/spec).

## Status

Proposed

## Consequences

Not applicable.
