# Architecture

This document describes the architecture of ibc-rs. If you're looking for a high-level overview of the code base, you've come to the right place!

## Bird's Eye View

![](docs/architecture/assets/repo-context.png)

At its highest level, `ibc-rs` defines the InterBlockChain protocol via [specifications](ibc-specs) and exposes modules that implement the specified protocol logic. The IBC protocol can be split between on-chain and off-chain processes. The main off-chain component is Hermes, which is a packet relayer that facillitates communication between two chains. The main on-chain components deal with the concepts of clients, connections, and channels. 

## How to Read the Codebase

`ibc-rs` (as well as many of Informal's other codebases) is structured a little bit differently from what you might see in a more "traditional" open source codebase. The main differentiating factor is the fact that the different pieces and components are specified in [standards](ibc-standards).

Answer how to read the codebase, i.e. `icsxx_`

## Code Map 

This section talks briefly about the various directories and modules in `ibc-rs`. 

### `modules`

This crate contains the main data structures and on-chain logic of the IBC protocol. These are the fundamental pieces that make up the IBC protocol. There is the conceptual notion of 'handlers', which are pieces of code that each handle a particular type of message. The most notable handlers are the [client](ibc-client), [connection](ibc-connection), and [channel](ibc-channel) handlers.  

#### Clients

Clients encapsulate all of the verification methods of another IBC-enabled chain in order to ensure that the other chain adheres to the IBC protocol and does not exhibit misbehaviour. Clients "track" the metadata of the other chain's blocks, and each chain has a client for every other chain that it communicates with. 

#### Connections

Connections associate a chain with another chain by connecting a client on the local chain with a client on the remote chain. This association is pair-wise unique and is established between two chains following a 4-step handshake process. 

#### Channels

Channels are an abstraction layer that facilitate communication between applications and the chains those applications depend upon. One important function that channels fulfill is guaranteeing that data packets sent between an application and its chain are well-ordered. 

### `relayer`

This crate provides the logic for relaying datagrams between chains. The process of relaying packets is kicked off by submitting transactions to read from or write to an IBC-enabled chain's state. More broadly, a relayer enables a chain to ascertain another chain's state by accessing its clients, connections, channels, or anything that is IBC-related.

### `relayer-cli`

A CLI wrapper around the `relayer` crate for running and issuing commands to a chain via a relayer. This crate exposes the Hermes binary. 

### `relayer-rest`

An add-on to the CLI mainly for exposing some internal runtime details of Hermes for debugging and observability reasons. 

### `proto`

Consists of protobuf-generated Rust types which are necessary for interacting with the Cosmos SDK. Also contains client and server methods that the relayer library includes for accessing the gRPC calls of a chain.

### `proto-compiler`

CLI tool to automate the compilation of proto buffers, which allows Hermes developers to go from a type specified in proto files to generate client gRPC code or server gRPC code.

### `telemetry`

Used by Hermes to gather telemetry data and expose it via a Prometheus endpoint.

## Cross-Cutting Concerns

### Testing

TODO

### Error Handling 

TODO 

[ibc-specs]: https://github.com/cosmos/ibc#interchain-standards
[ibc-standards]: https://github.com/cosmos/ibc#standardisation
[ibc-client]: https://github.com/informalsystems/ibc-rs/tree/master/modules/src/ics02_client
[ibc-connection]: https://github.com/informalsystems/ibc-rs/tree/master/modules/src/ics03_connection
[ibc-channel]: https://github.com/informalsystems/ibc-rs/tree/master/modules/src/ics04_channel

