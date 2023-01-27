# Features

This section includes a summary of the supported and planned features. It also includes a feature matrix which compares `hermes` to the [cosmos-go-relayer].

> **Cosmos SDK & IBC compatibility:**
> Hermes supports Cosmos SDK chains implementing the [IBC protocol v1][ibcv1-proto] protocol specification.
> Cosmos SDK versions `0.41.3` through `0.45.x` are officially supported.
> IBC-go versions `1.1.*` thorough `3.*` are officially supported.
> In case Hermes finds an incompatible SDK or IBC-go version, it will output a log warning upon initialization as part of the `start` command or upon `health-check` command.

---

## Supported Features

- Basic features
    - Create and update clients.
    - Refresh clients to prevent expiration.
    - Establish connections with new or existing clients.
    - Establish channels with new or existing connection.
    - Channel closing handshake.
    - Relay packets, acknowledgments, timeout and timeout-on-close packets, with zero or non-zero delay.
    - Queries for all objects.
- Packet relaying over:
    - multiple paths, for the chains in `config.toml`.
- Restart support:
    - Clear packets.
    - Resume channel handshake if configured to relay `all`.
    - Resume connection handshake if configured to relay `all`.
- Client upgrade:
    - Upgrading clients after a counterparty chain has performed an upgrade for IBC breaking changes.
- Packet delay:
    - Establish path over non-zero delay connection.
    - Relay all packets with the specified delay.
- Interchain Accounts & Interchain Security
    > Relaying between Interchain Security-enabled chains requires Hermes v1.2+.
- Monitor and submit misbehaviour for clients
    - Monitor client updates for misbehaviour (fork and BFT time violation).
    - Submit misbehaviour evidence to the on-chain IBC client.
    > Misbehaviour submission to full node not yet supported.
- Individual commands that build and send transactions for:
    - Creating and updating IBC Tendermint light clients.
    - Sending connection open handshake messages.
    - Sending channel open handshake messages.
    - Sending channel closing handshake messages.
    - Initiating a cross chain transfer (mainly for testing).
    - Relaying sent packets, acknowledgments and timeouts.
    - Automatically generate a configuration file from the [chain-registry](https://github.com/cosmos/chain-registry)
    - Client upgrade.
- Channel handshake for existing channel that is not in `Open` state.
- Connection handshake for existing connection that is not in `Open` state.
- Telemetry support.

## Upcoming / Unsupported Features

Planned features:
- Interchain Queries
- Non-SDK support
- Relay from all IBC events, including governance upgrade proposal
- Dynamic & automatic configuration management

## Features matrix

---

__Legend__:

| Term              | Description                                                                                      |
| -----             | -----------                                                                                      |
| ❌                | feature not supported                                                                            |
| ✅                | feature is supported                                                                             |
| `Chain`           | chain related                                                                                    |
| `Cl`              | client related                                                                                   |
| `Conn`            | connection related                                                                               |
| `Chan`            | channel related                                                                                  |
| `Cfg`             | config related                                                                                  |
| `.._Handshake_..` | can execute all transactions required to finish a handshake from a single command                |
| `.._<msg>_A`      | building and sending `msg` from a command that scans chain state                                 |
| `.._<msg>_P`      | building and sending `msg` from IBC event; doesn't apply to `.._Init` and `FT_Transfer` features |

--- 
__Feature comparison between Hermes and the Go relayer__ 

| Features \      Status | Hermes | Cosmos Go | Feature Details  |
| ---------------------- | :---: | :----: |:-------|
| Restart                | ✅    | ✅     | replays any IBC events that happened before restart
| Multiple_Paths         | ✅    | ✅     | relays on multiple paths concurrently
|                        |       |        |
| Connection Delay       | ✅    | ❌     | 
| Cl_Misbehavior         | ✅    | ❌     | monitors and submits IBC client misbehavior
| Cl_Refresh             | ✅    | ✅     | periodically refresh an on-chain client to prevent expiration
| Packet Delay           | ✅    | ❌     | 
|                        |       |        |
| Chan_Unordered         | ✅    | ✅     |
| Chan_Ordered           | ✅    | ✅     |
|                        |       |        |
| Cl_Tendermint_Create   | ✅    | ✅     | tendermint light client creation
| Cl_Tendermint_Update   | ✅    | ✅     | tendermint light client update
| Cl_Tendermint_Upgrade  | ✅    | ✅     | tendermint light client upgrade
|                        |       |        |
| Conn_Open_Handshake_A  | ✅    | ✅     |
| Conn_Open_Handshake_P  | ✅    | ✅     |
|                        |       |        |
| Chan_Open_Handshake_A  | ✅    | ✅     |
| Chan_Open_Handshake_P  | ✅    | ✅     |
| Chan_Open_Handshake_Optimistic  | ❌    | ❌     | open a channel on a non-Open connection
|                        |       |        |
| Chan_Close_Handshake_P | ✅    | ✅     | 
| Chan_Close_Handshake_A | ✅    | ✅     |
|                        |       |        |
| FT_Transfer            | ✅    | ✅     | can submit an ICS-20 fungible token transfer message
| ICA_Relay               | ✅    | ✅     | can relay ICS-27 Interchain account packets
| Packet_Recv_A          | ✅    | ✅     |
| Packet_Recv_P          | ✅    | ✅     |
| Packet_Timeout_A       | ✅    | ✅     |
| Packet_Timeout_P       | ✅    | ✅     |
| Packet_TimeoutClose_A  | ✅    | ✅     |
| Packet_TimeoutClose_P  | ✅    | ✅     |
| Packet_Optimistic      | ❌    | ❌     | relay packets over non-Open channels
|                        |       |        |
| Cl_Non_Tendermint      | ❌    | ❌     | supports non tendermint IBC light clients
| Chain_Non_Cosmos       | ❌    | ❌     | supports non cosmos-SDK chains
|                        |       |        |
| Cfg_Static            | ✅    | ✅     | provides means for configuration prior to being started
| Cfg_Dynamic           | ❌    | ❌     | provides means for configuration and monitoring during runtime
| Cfg_Download_Config   | ✅    | ✅     | provides means for downloading recommended configuration 
| Cfg_Edit_Config       | ❌    | ✅     | provides means for editing the configuration from the CLI 
| Cfg_Validation        | ✅    | ✅     | provides means to validate the current configuration 
| Telemetry             | ✅    | ✅     | telemetry server to collect metrics 
| REST API              | ✅    | ❌     | REST API to interact with the relayer 


[cosmos-go-relayer]: https://github.com/cosmos/relayer
[ibcv1-proto]: https://github.com/cosmos/ibc
