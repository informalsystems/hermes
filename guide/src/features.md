# Features

This section includes a summary of the supported and planned features.
A feature matrix and comparison between the Rust and Go relayer implementations can be found in the [Feature Matrix](./features/matrix.md)

> **Cosmos SDK & IBC compatibility:**
> Hermes supports Cosmos SDK chains implementing the [IBC protocol v1][ibcv1-proto] protocol specification.
> Cosmos SDK versions `0.41.3` through `0.45.x` are officially supported.
> IBC-go versions `1.1.*` thorough `3.*` are officially supported.
> In case Hermes finds an incompatible SDK or IBC-go version, it will output a log warning upon initialization as part of the `start` command or upon `health-check` command.

[ibcv1-proto]: https://github.com/cosmos/ibc

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
- Interchain Accounts & Interchain Security
- Monitor and submit misbehaviour for clients
    - monitor client updates for misbehaviour (fork and BFT time violation)
    - submit misbehaviour evidence to the on-chain IBC client.
    > misbehaviour submission to full node not yet supported
- Individual commands that build and send transactions for:
    - creating and updating IBC Tendermint light clients
    - sending connection open handshake messages
    - sending channel open handshake messages
    - sending channel closing handshake messages
    - initiating a cross chain transfer (mainly for testing)
    - relaying sent packets, acknowledgments and timeouts
    - client upgrade
- Channel handshake for existing channel that is not in `Open` state
- Connection handshake for existing connection that is not in `Open` state
- Telemetry support

## Upcoming / Unsupported Features

Planned features:
- Interchain Queries
- Non-SDK support
- Relay from all IBC events, including governance upgrade proposal
- Dynamic & automatic configuration management