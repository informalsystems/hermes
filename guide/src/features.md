# Features

This section includes a summary of the supported and planned features.
A feature matrix and comparison between the Rust and Go relayer implementations can be found in the [Feature Matrix](./features/matrix.md)

> **Cosmos SDK compatibility:**
> Hermes supports Cosmos SDK chains implementing the [IBC v1.1][ibcv1] protocol specification.
> Cosmos SDK versions `0.41.3` to `0.44.x` are officially supported.
> In case Hermes finds an incompatible SDK version, it will output a log warning.

[ibcv1]: https://github.com/cosmos/ibc-go

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
    - multiple paths, for the chains in `config.toml`
- Restart support
    - clear packets
    - resume channel handshake if configured to relay `all`
    - resume connection handshake if configured to relay `all`
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
- Channel handshake for existing channel that is not in `Open` state
- Connection handshake for existing connection that is not in `Open` state
- Telemetry support

## Upcoming / Unsupported Features

Planned features:
- Full Passive mode: relay from all IBC events
    - Connection handshake for existing connection that is not in `Open` state
- Relayer support for management application (add RPC server)
- Dynamic configuration management

Not planned:
- Relayer management application
- Create clients with user chosen parameters (such as UpgradePath)
- Use IBC light clients other than Tendermint such as Solo Machine
- Support non cosmos-SDK chains
