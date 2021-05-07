# Features

This section includes a summary of the supported and planned features.
A feature matrix and comparison between the Rust and Go relayer implementations can be found in the [Feature Matrix](./features/matrix.md)

## Supported Features

- Basic features
    - create and update clients
    - refresh clients to prevent expiration
    - establish connections with new or existing clients
    - establish channels with new or existing connection
    - channel closing handshake
    - relay packets, acknowledgments, timeout and timeout-on-close packets, with zero or non-zero delay.
    - queries for all objects
- Packet relaying over:
    - new path
    - single specified path
    - multiple paths, for the chains in `config.toml`
- Restart support
    - clear packets on relayer restart when started for a single path or multiple paths
- Client upgrade
    - upgrading clients after a counterparty chain has performed an upgrade for IBC breaking changes
- Packet delay:
    - establish path over non-zero delay connection
    - relay all packets with the specified delay
- Monitor and submit misbehaviour for clients
    - monitor client updates for misbehaviour (fork and BFT time violation)
    - submit misbehaviour evidence to the on-chain IBC client.
    > misbehaviour submission to full node not yet supported
- Individual commands that build and send transactions for:
    - creating and updating IBC Tendermint light clients
    - sending connection open handshake datagrams
    - sending channel open handshake datagrams
    - sending channel closing handshake datagrams
    - initiating a cross chain transfer (mainly for testing)
    - relaying sent packets, acknowledgments and timeouts
    - client upgrade

## Upcoming / Unsupported Features

Planned features:
- Connection handshake for existing connection that is not in `Open` state
- Channel handshake for existing channel that is not in `Open` state
- Full Passive mode: relay from all IBC events
- Relayer support for management application (add RPC server)
- Telemetry support
- Dynamic configuration management

Not planned:
- Relayer management application
- Create clients with user chosen parameters (such as UpgradePath)
- Use IBC light clients other than Tendermint such as Solo Machine
- Support non cosmos-SDK chains
