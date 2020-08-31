# Changelog

## v0.0.3

*September 1, 2020*

This release focuses mostly on the IBC handler framework and implementation of ICS02 and ICS07.

### BREAKING CHANGES:
  
### FEATURES:
- [modules] Proposal for IBC handler architecture and partial implementation of ICS02 and ICS03 message handlers.
        [\#197](https://github.com/informalsystems/ibc-rs/pull/197),
- [spec] Detailed technical specification of the relayer algorithm with focus on client update [\#110](https://github.com/informalsystems/ibc-rs/pull/110)
- [spec] Documentation for the repository structure [\#100](https://github.com/informalsystems/ibc-rs/pull/100)

### IMPROVEMENTS:

- [modules] Cleanup
        [\#200](https://github.com/informalsystems/ibc-rs/pull/200),
        [\#203](https://github.com/informalsystems/ibc-rs/pull/203),
- [modules and relayer-clie] Refactor ConnectionId decoding
        [\#196](https://github.com/informalsystems/ibc-rs/pull/196),
- [modules] Alignment with recent ICS changes in identifiers
        [\#189](https://github.com/informalsystems/ibc-rs/pull/189),
           
### BUG FIXES:


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

