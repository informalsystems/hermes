# Changelog

## v0.0.3
*September 1, 2020*

This release focuses on the IBC message processor framework and initial
implementations in ICS02 and ICS07. It also introduces an initial specification for the relayer algorithm.

Other highlights:
- The modules crate is published as [ibc](https://crates.io/crates/ibc) in crates.io
- ADR-001 and ADR-003 are complete. 🎉

### BREAKING CHANGES:
- [modules] Renamed `modules` crate to `ibc` crate. Version number for the new crate is not reset. ([#198])
- [modules/ics02] `ConnectionId`s are now decoded to `Vec<ConnectionId>` and validated instead of `Vec<String>` ([#185])
- [modules/ics03] Removed `Connection` and `ConnectionCounterparty` traits ([#193])
- [modules/ics04] Removed `Channel` and `ChannelCounterparty` traits ([#192])

### FEATURES:
- [modules/ics02] partial implementation of message handler ([#119], [#194])
- [modules/ics07] partial implementation of message handler ([#119], [#194])
- [architecture/ADR-003] Proposal for IBC handler (message processor) architecture ([#119], [#194])
- [spec/relayer] Detailed technical specification of the relayer algorithm with focus on client update ([#84])
- [architecture/ADR-001] Documentation for the repository structure ([#1])
- [architecture/FSM-1] Connection Handshake FSM English description ([#122])

### IMPROVEMENTS:
- [contributing] Updated CONTRIBUTING.md. Please read before opening PRs ([#195])
- [relayer-cli] Refactor ConnectionId decoding in `query client` ([#185])

### BUG FIXES:
- [modules/ics24] Identifiers limit update according to ICS specs ([#168])

[spec/relayer]: https://github.com/informalsystems/ibc-rs/blob/master/docs/spec/relayer/Relayer.md
[#84]: https://github.com/informalsystems/ibc-rs/issues/84
[architecture/ADR-001]: https://github.com/informalsystems/ibc-rs/blob/master/docs/architecture/adr-001-repo.md
[#1]: https://github.com/informalsystems/ibc-rs/issues/1
[contributing]: https://github.com/informalsystems/ibc-rs/blob/master/CONTRIBUTING.md
[#195]: https://github.com/informalsystems/ibc-rs/pull/195
[modules]: https://github.com/informalsystems/ibc-rs/tree/master/modules
[#198]: https://github.com/informalsystems/ibc-rs/issues/198
[modules/ics02]: https://github.com/informalsystems/ibc-rs/tree/master/modules/src/ics02_client
[#185]: https://github.com/informalsystems/ibc-rs/issues/185
[modules/ics03]: https://github.com/informalsystems/ibc-rs/tree/master/modules/src/ics03_connection
[#193]: https://github.com/informalsystems/ibc-rs/issues/193
[modules/ics04]: https://github.com/informalsystems/ibc-rs/tree/master/modules/src/ics04_channel
[#192]: https://github.com/informalsystems/ibc-rs/issues/192
[relayer-cli]: https://github.com/informalsystems/ibc-rs/tree/master/relayer-cli
[architecture/FSM-1]: https://github.com/informalsystems/ibc-rs/blob/master/docs/architecture/fsm-async-connection.md
[#122]: https://github.com/informalsystems/ibc-rs/issues/122
[architecture/ADR-003]: https://github.com/informalsystems/ibc-rs/blob/master/docs/architecture/adr-003-handler-implementation.md
[#119]: https://github.com/informalsystems/ibc-rs/issues/119
[#194]: https://github.com/informalsystems/ibc-rs/issues/194
[modules/ics24]: https://github.com/informalsystems/ibc-rs/tree/master/modules/src/ics24_host
[#168]: https://github.com/informalsystems/ibc-rs/issues/168
[modules/ics07]: https://github.com/informalsystems/ibc-rs/tree/master/modules/src/ics07_tendermint

## v0.0.2

*August 1, 2020*

This release is focused on updating the query system from amino to protobuf,
implementing a few queries from the CLI, and establishing an initial testing framework
that will support multiple chain types.

It does not target a stable release of Cosmos-SDK chains, but is tracking
the latest state of development towards the Cosmos-SDK Stargate release.

### BREAKING CHANGES:

- [modules|relayer] Refactor queries, paths, and Chain trait to reduce code and use
  protobuf instead of Amino.
        [\#152](https://github.com/informalsystems/ibc-rs/pull/152),
        [\#174](https://github.com/informalsystems/ibc-rs/pull/174),
        [\#155](https://github.com/informalsystems/ibc-rs/pull/155)
- [repo] Moved relayer/cli to relayer-cli, relayer/relay to relayer. [\#183](https://github.com/informalsystems/ibc-rs/pull/183)
  
### FEATURES:

- [relayer] Query connections given client id. [\#169](https://github.com/informalsystems/ibc-rs/pull/169)
- [relayer] Query connection given connection id. [\#136](https://github.com/informalsystems/ibc-rs/pull/136)
- [relayer] Query channel given channel id and port [\#163](https://github.com/informalsystems/ibc-rs/pull/163)
- [spec] Channel closing datagrams in TLA+ [\#141](https://github.com/informalsystems/ibc-rs/pull/141)

### IMPROVEMENTS:

- [ci] Framework (scripts and Github Actions) for integration testing the relayer queries against 
    the Cosmos-SDK's `simd` binary with prepopulated IBC state in the genesis
        [\#140](https://github.com/informalsystems/ibc-rs/pull/140),
        [\#184](https://github.com/informalsystems/ibc-rs/pull/184)
- [relayer|modules] Implemented better Raw type handling. [\#156](https://github.com/informalsystems/ibc-rs/pull/156)
- [repo] Add rust-toolchain file. [\#154](https://github.com/informalsystems/ibc-rs/pull/154)
   
### BUG FIXES:

- [modules] Fixed the identifiers limits according to updated ics spec. [\#189](https://github.com/informalsystems/ibc-rs/pull/189)
- [modules/relayer] Remove some warnings triggered during compilation due to dependency specification. [\#132](https://github.com/informalsystems/ibc-rs/pull/132)
- [modules] Fix nightly runs. [\#161](https://github.com/informalsystems/ibc-rs/pull/161)
- [repo] Fix for incomplete licence terms. [\#153](https://github.com/informalsystems/ibc-rs/pull/153)
  
## 0.0.1

*July 1st, 2020*

This is the initial prototype release of an IBC relayer and TLA+ specifications.
There are no compatibility guarantees until v0.1.0.

Includes:

- Configuration file definition and validation
- Client state, consensus state, connection, channel queries.
    - Note: deserialization is unimplemented as it has dependency on migration to protobuf for ABCI queries
- Per chain light clients threads are created and headers are periodically retrieved and verified.
- Per chain IBC event monitor threads are spawned and main event handler that receives them.
    - Note: the event handler just displays the events.
- IBC Modules partial implementation for datastructures, messages and queries.
- Some English and TLA+ specifications for Connection & Channel Handshake as well as naive relayer algorithm.
