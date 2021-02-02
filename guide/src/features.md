# Features
[WIP]
## Supported Features

- establish a new relaying path (new clients, connection and unordered channel handshake)
- relay from packet events on a newly created, or an existing relaying path

  __Limitations:__
   - only one path per relayer instance
   - relayer restart is not supported, i.e. pending packets (previously sent packets and acknowledgments) are not cleared on startup

- raw commands for:
    - creating and updating IBC Tendermint light clients
    - sending connection open handshake datagrams
    - sending channel open handshake datagrams
    - sending channel closing handshake datagrams
    - initiating a cross chain transfer (mainly for testing)
    - relaying sent packets, acknowledgments and timeouts

## Upcoming/ Unsupported Features

Planned features:
- support for client upgrade and unfreezing
- connection handshake using existing clients and/or existing connection that is not in `Open` state
- channel handshake using existing clients, opened connection, and/ or existing channel that is not in `Open` state
- relay from IBC events for multiple connection and channels
- support for relayer restart
- close-to-0 configuration relayer
- relayer support for management application (add RPC server)

TBD:
- relayer management application
- create clients with user chosen parameters (such as UpgradePath)
- monitor and submit misbehaviour for clients
- use IBC light clients other than Tendermint such as Solo Machine
- support non-cosmos-SDK chains
- submit IBC client unfreezing proposals
- sending an UpgradePlan proposal for an IBC breaking upgrade
- upgrading clients after a counterparty chain has performed an upgrade for IBC breaking changes
