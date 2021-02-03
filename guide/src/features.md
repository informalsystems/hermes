# Features

This section includes a summary of the supported and planned features.
More details and feature comparison between the Rust and Go relayer implementations can be found in the [Feature Matrix](./feature_matrix.md)

## Supported Features

- establish a new relaying path (new clients, connection and unordered channel handshake)
- relay from packet events on a newly created, or an existing relaying path

  __Limitations:__
   - only one path per relayer instance
   - relayer restart is not supported, i.e. pending packets (previously sent packets and acknowledgments) are not cleared on startup

- individual commands that build and send transactions for:
    - creating and updating IBC Tendermint light clients
    - sending connection open handshake datagrams
    - sending channel open handshake datagrams
    - sending channel closing handshake datagrams
    - initiating a cross chain transfer (mainly for testing)
    - relaying sent packets, acknowledgments and timeouts

## Upcoming / Unsupported Features

Planned features:
- support for client upgrade and unfreezing
- connection handshake using existing clients and/or existing connection that is not in `Open` state
- channel handshake using existing clients, opened connection, and/ or existing channel that is not in `Open` state
- passive mode: relay from all IBC events
- support for relayer restart
- support for multiple paths
- close-to-0 configuration relayer
- relayer support for management application (add RPC server)

Not planned:
- relayer management application
- create clients with user chosen parameters (such as UpgradePath)
- monitor and submit misbehaviour for clients
- use IBC light clients other than Tendermint such as Solo Machine
- support non cosmos-SDK chains
- sending an UpgradePlan proposal for an IBC breaking upgrade
- upgrading clients after a counterparty chain has performed an upgrade for IBC breaking changes
