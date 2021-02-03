# Features

This section includes a summary of the supported and planned features.
More details and feature comparison between the Rust and Go relayer implementations can be found in the [Feature Matrix](./feature_matrix.md)

## Supported Features

- Establish a new relaying path (new clients, connection and unordered channel handshake)
- Relay from packet events on a newly created, or an existing relaying path

  __Limitations:__
   - Only one path per relayer instance
   - Relayer restart is not supported, i.e. pending packets (previously sent packets and acknowledgments) are not cleared on startup

- individual commands that build and send transactions for:
    - Creating and updating IBC Tendermint light clients
    - Sending connection open handshake datagrams
    - Sending channel open handshake datagrams
    - Sending channel closing handshake datagrams
    - Initiating a cross chain transfer (mainly for testing)
    - Relaying sent packets, acknowledgments and timeouts

## Upcoming / Unsupported Features

Planned features:
- Support for client upgrade and unfreezing
- Connection handshake using existing clients and/or existing connection that is not in `Open` state
- Channel handshake using existing clients, opened connection, and/ or existing channel that is not in `Open` state
- Passive mode: relay from all IBC events
- Support for relayer restart
- Support for multiple paths
- Close-to-0 configuration relayer
- Relayer support for management application (add RPC server)

Not planned:
- Relayer management application
- Create clients with user chosen parameters (such as UpgradePath)
- Monitor and submit misbehaviour for clients
- Use IBC light clients other than Tendermint such as Solo Machine
- Support non cosmos-SDK chains
- Sending an UpgradePlan proposal for an IBC breaking upgrade
- Upgrading clients after a counterparty chain has performed an upgrade for IBC breaking changes
