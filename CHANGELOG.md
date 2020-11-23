# Changelog

## Unreleased Changes

Special thanks to external contributors for this release: @CharlyCst ([#347]).

### FEATURES

- Update Tokio to version 0.3 ([#402])
- Update to tendermint-rs version `0.17-RC3` ([#403])
- [changelog] Added "unreleased" section in `CHANGELOG.MD` to help streamline releases ([#274])
- [relayer] Integrate relayer spike into relayer crate ([#335])
- [modules]
    - Implement flexible connection id selection ([#332])
    - ICS 4 Domain Types for channel handshakes and packets ([#315], [#95])
    - Introduce LightBlock support for MockContext ([#389])
- [relayer] 
    - Implement `query_header_at_height` via plain RPC queries (no light client verification) ([#336])
    - Implement the relayer logic for connection handshake messages ([#358], [#359], [#360])
    - Implement the relayer logic for channel handshake messages ([#371], [#372], [#373], [#374])
- [relayer-cli]
    - Merge light clients config in relayer config and add commands to add/remove light clients ([#348])
    - CLI for client update message ([#277])
    - Implement the relayer CLI for connection handshake messages ([#358], [#359], [#360])
    - Implement the relayer CLI for channel handshake messages ([#371], [#372], [#373], [#374])
    - Implement commands to add and list keys for a chain ([#363])
- [proto-compiler]
    - Refactor and allow specifying a commit at which the Cosmos SDK should be checked out ([#366])
    - Add a `--tag` option to the `clone-sdk` command to check out a tag instead of a commit ([#369])
- [ibc-proto] Refactor and allow specifying a commit at which the Cosmos SDK should be checked out ([#366])

[#95]: https://github.com/informalsystems/ibc-rs/issues/95
[#274]: https://github.com/informalsystems/ibc-rs/issues/274
[#315]: https://github.com/informalsystems/ibc-rs/issues/315
[#332]: https://github.com/informalsystems/ibc-rs/issues/332
[#335]: https://github.com/informalsystems/ibc-rs/pulls/335
[#336]: https://github.com/informalsystems/ibc-rs/issues/336
[#348]: https://github.com/informalsystems/ibc-rs/pulls/348
[#358]: https://github.com/informalsystems/ibc-rs/issues/358
[#358]: https://github.com/informalsystems/ibc-rs/issues/359
[#358]: https://github.com/informalsystems/ibc-rs/issues/360
[#363]: https://github.com/informalsystems/ibc-rs/issues/363
[#366]: https://github.com/informalsystems/ibc-rs/issues/366
[#368]: https://github.com/informalsystems/ibc-rs/issues/368
[#369]: https://github.com/informalsystems/ibc-rs/pulls/369
[#371]: https://github.com/informalsystems/ibc-rs/issues/371
[#372]: https://github.com/informalsystems/ibc-rs/issues/372
[#373]: https://github.com/informalsystems/ibc-rs/issues/373
[#374]: https://github.com/informalsystems/ibc-rs/issues/374
[#389]: https://github.com/informalsystems/ibc-rs/issues/389
[#402]: https://github.com/informalsystems/ibc-rs/issues/402
[#403]: https://github.com/informalsystems/ibc-rs/issues/403
[proto-compiler]: https://github.com/informalsystems/ibc-rs/tree/master/proto-compiler

### IMPROVEMENTS

- [relayer-cli]
    - Split tasks spawned by CLI commands into their own modules ([#331])
    - V0 command implementation ([#346])
- [modules]
    - Homogenize ConnectionReader trait so that all functions return owned objects ([#347])
    - Align with tendermint-rs in the domain type definition of `block::Id` ([#338])

[#274]: https://github.com/informalsystems/ibc-rs/issues/274
[#277]: https://github.com/informalsystems/ibc-rs/issues/277
[#331]: https://github.com/informalsystems/ibc-rs/pulls/331
[#332]: https://github.com/informalsystems/ibc-rs/issues/332
[#335]: https://github.com/informalsystems/ibc-rs/pulls/335
[#336]: https://github.com/informalsystems/ibc-rs/issues/336
[#338]: https://github.com/informalsystems/ibc-rs/issues/338
[#347]: https://github.com/informalsystems/ibc-rs/issues/347
[#346]: https://github.com/informalsystems/ibc-rs/issues/346
[#348]: https://github.com/informalsystems/ibc-rs/pulls/348
[changelog]: https://github.com/informalsystems/ibc-rs/tree/master/CHANGELOG.md

## v0.0.4
*October 19, 2020*

This release focuses on alignment with the Cosmos ecosystem: adaptations to Tendermint-rs 0.16 and subsequently to 0.17 (`0.17.0-rc1`), and numerous protobuf updates following latest stargate releases.

Additional highlights:
- Adding DomainTypes and (de)serialization capability to ICS02 and ICS03 messages and structures.
- Improvements of the IBC message processor framework (handlers, contexts and mocks).
- Added initial implementations for the ICS26 (routing module) and ICS18 (basic relayer algorithms module) for use in testing.
- Also added support for packet handling in the relayer algorithm specifications.

### BREAKING CHANGES:
- [relayer] & [modules] Alignment with ecosystem updates:
    - Compatibility with the latest protobuf (Gaia stargate-3 and stargate-4) ([#191], [#272], [#273], [#278]) 
    - Adaptations to tendermint 0.17 ([#286], [#293], [#300], [#302], [#308])
- [relayer] UX improvement: Remove proof option from client connections command ([#205])

### FEATURES:
- [modules/ics03] ICS03 Ack and Confirm message processors ([#223])
- [relayer-cli]
    - Relayer CLIs for client messages ([#207])
    - Relayer CLIs for connection-open-init ([#206])
    - Queries for consensus state and client state ([#149], [#150])
- [modules] Routing module minimal implementation for MVP ([#159], [#232])
- [spec/relayer] Relayer specification for packet handling ([#229], [#234], [#237])
- [spec/relayer] Basic packet handling in TLA+([#124])
- [modules] Basic relayer functionality: a test with ClientUpdate ping-pong between two mocked chains ([#276])

### IMPROVEMENTS:
- [modules] Implemented the `DomainType` trait for IBC proto structures ([#245], [#249]).
- [modules] & [ibc-proto] Several improvements to message processors, among which ([#218]):
    - ICS03 connection handshake protocol initial implementation and tests ([#160])
    - Add capability to decode from protobuf Any* type into Tendermint and Mock client states 
    - Cleanup Any* client wrappers related code
    - Migrate handlers to newer protobuf definitions ([#226])
    - Extend client context mock ([#221])
    - Context mock simplifications and cleanup ([#269], [#295], [#296], [#297])
- [modules/ics03] Split `msgs.rs` in multiple files, implement `From` for all messages ([#253])
- [ibc-proto]
    - Move ibc-proto source code into ibc-rs ([#142]) and fixed code deduplication ([#282], [#284])
    - Consolidate proto-compiler logic [#241]
- [spec/relayer] Add support for APALACHE to the Relayer TLA+ spec ([#165])
- [relayer] Update to tendermint v.0.16 and integrate with the new light client implementation ([#90], [#243])

### BUG FIXES:
- [modules] Removed "Uninitialized" state from connection ([#217])
- [relayer-cli] Fix for client query subcommands ([#231])
- [disclosure-log] & [spec/connection-handshake] Disclosed bugs in ICS3 version negotiation and proposed a fix ([#209], [#213])

[#90]: https://github.com/informalsystems/ibc-rs/issues/90
[#124]: https://github.com/informalsystems/ibc-rs/issues/124
[#142]: https://github.com/informalsystems/ibc-rs/issues/142
[#149]: https://github.com/informalsystems/ibc-rs/issues/149
[#150]: https://github.com/informalsystems/ibc-rs/issues/150
[#159]: https://github.com/informalsystems/ibc-rs/issues/159
[#160]: https://github.com/informalsystems/ibc-rs/issues/160
[#165]: https://github.com/informalsystems/ibc-rs/issues/165
[#191]: https://github.com/informalsystems/ibc-rs/issues/191
[#205]: https://github.com/informalsystems/ibc-rs/issues/205
[#206]: https://github.com/informalsystems/ibc-rs/issues/206
[#207]: https://github.com/informalsystems/ibc-rs/issues/207
[#209]: https://github.com/informalsystems/ibc-rs/issues/209
[#213]: https://github.com/informalsystems/ibc-rs/issues/213
[#217]: https://github.com/informalsystems/ibc-rs/issues/217
[#218]: https://github.com/informalsystems/ibc-rs/issues/218
[#221]: https://github.com/informalsystems/ibc-rs/issues/221
[#223]: https://github.com/informalsystems/ibc-rs/issues/223
[#226]: https://github.com/informalsystems/ibc-rs/issues/226
[#229]: https://github.com/informalsystems/ibc-rs/issues/229
[#231]: https://github.com/informalsystems/ibc-rs/issues/231
[#232]: https://github.com/informalsystems/ibc-rs/issues/232
[#234]: https://github.com/informalsystems/ibc-rs/issues/234
[#237]: https://github.com/informalsystems/ibc-rs/issues/237
[#241]: https://github.com/informalsystems/ibc-rs/issues/241
[#243]: https://github.com/informalsystems/ibc-rs/issues/243
[#245]: https://github.com/informalsystems/ibc-rs/issues/245
[#249]: https://github.com/informalsystems/ibc-rs/issues/249
[#253]: https://github.com/informalsystems/ibc-rs/issues/253
[#269]: https://github.com/informalsystems/ibc-rs/issues/269
[#272]: https://github.com/informalsystems/ibc-rs/issues/272
[#273]: https://github.com/informalsystems/ibc-rs/issues/273
[#276]: https://github.com/informalsystems/ibc-rs/issues/276
[#278]: https://github.com/informalsystems/ibc-rs/issues/278
[#282]: https://github.com/informalsystems/ibc-rs/issues/282
[#284]: https://github.com/informalsystems/ibc-rs/issues/284
[#286]: https://github.com/informalsystems/ibc-rs/issues/286
[#293]: https://github.com/informalsystems/ibc-rs/issues/293
[#295]: https://github.com/informalsystems/ibc-rs/issues/295
[#296]: https://github.com/informalsystems/ibc-rs/issues/296
[#297]: https://github.com/informalsystems/ibc-rs/issues/297
[#300]: https://github.com/informalsystems/ibc-rs/issues/300
[#302]: https://github.com/informalsystems/ibc-rs/issues/302
[#308]: https://github.com/informalsystems/ibc-rs/issues/308
[ibc-proto]: https://github.com/informalsystems/ibc-rs/tree/master/proto
[disclosure-log]: https://github.com/informalsystems/ibc-rs/blob/master/docs/disclosure-log.md
[spec/connection-handshake]: https://github.com/informalsystems/ibc-rs/tree/master/docs/spec/connection-handshake
[relayer]: https://github.com/informalsystems/ibc-rs/tree/master/relayer

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
