# Features

This section includes a summary of the supported and planned features.
More details and feature comparison between the Rust and Go relayer implementations can be found in the [Feature Matrix](./features/matrix.md)

## Supported Features
- Create and update clients
- Establish connections with new or existing clients
- Establish channels with new or existing connection
- Relay packets, acknowledgments, timeout and timeout-on-close packets, with zero or non-zero delay.
- Relay packets over multiple paths
- Clear packets on relayer restart when started for a single path
- Upgrading clients after a counterparty chain has performed an upgrade for IBC breaking changes
- Monitor and submit misbehaviour for clients

- Individual commands that build and send transactions for:
    - Creating and updating IBC Tendermint light clients
    - Sending connection open handshake datagrams
    - Sending channel open handshake datagrams
    - Sending channel closing handshake datagrams
    - Initiating a cross chain transfer (mainly for testing)
    - Relaying sent packets, acknowledgments and timeouts
    - Client upgrade

## Upcoming / Unsupported Features

Planned features:
- Connection handshake for existing connection that is not in `Open` state
- Channel handshake for existing channel that is not in `Open` state
- Clear pending packets in multi path mode
- Full Passive mode: relay from all IBC events
- Close-to-0 configuration relayer
- Relayer support for management application (add RPC server)

Not planned:
- Relayer management application
- Create clients with user chosen parameters (such as UpgradePath)
- Use IBC light clients other than Tendermint such as Solo Machine
- Support non cosmos-SDK chains
