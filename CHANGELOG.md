## [pending_version]

* Refactored `relayer/cli` into `relayer-cli` folder. ([#180](https://github.com/informalsystems/ibc-rs/issues/180))
* Refactored `relayer/relay` into `relayer` folder. ([#180](https://github.com/informalsystems/ibc-rs/issues/180))

## [0.0.1]

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

