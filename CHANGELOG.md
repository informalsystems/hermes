## [0.0.1] - 2020-07-01

- Initial release
### Added
- Configuration file definition and validation
- Client state, consensus state, connection, channel queries.

    - Note: deserialization is unimplemented as it has dependency on migration to protobuf for ABCI queries
- Per chain light clients threads are created and headers are periodically retrieved and verified.
- Per chain IBC event monitor threads are spawned and main event handler that receives them.

    - Note: the event handler just displays the events.
- IBC Modules partial implementation for datastructures, messages and queries.
- Some specifications and models for Connection Handshake and Naive relayer algorithm.