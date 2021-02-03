# Feature Matrix, Implementation Comparison

This section gives more details on some of the features and implementation status for the Hermes Rust and the Cosoms Go relayers.


| Features \      Status | Hermes | Cosmos Go |
| ---------------------- | :----: | :-------: |
| Restart                | ❌     | ✅        |
| Multiple-Paths         | ❌     | ✅        |
|                        |        |           |
| Cl-Tendermint-Create   | ✅     | ✅        |
| Cl-Tendermint-Update   | ✅     | ✅        |
| Cl-Tendermint-Upgrade  | ❌     | ✅        |
|                        |        |           |
| Conn-Handshake-A       | ✅     | ✅        |
| Conn-Handshake-P       | ❌     | ❌        |
| Chan-Handshake-A       | ✅     | ✅        |
| Chan-Handshake-P       | ❌     | ❌        |
|                        |        |           |
| Conn-Open-Init         | ✅     | ✅        |
| Conn-Open-Try-A        | ✅     | ✅        |
| Conn-Open-Try-P        | ❌     | ❌        |
| Conn-Open-Ack-A        | ✅     | ✅        |
| Conn-Open-Ack-P        | ❌     | ❌        |
| Conn-Open-Confirm-A    | ✅     | ✅        |
| Conn-Open-Confirm-P    | ❌     | ❌        |
|                        |        |           |
| Chan-Open-Init         | ✅     | ✅        |
| Chan-Open-Try-A        | ✅     | ✅        |
| Chan-Open-Try-P        | ❌     | ❌        |
| Chan-Open-Ack-A        | ✅     | ✅        |
| Chan-Open-Ack-P        | ❌     | ❌        |
| Chan-Open-Confirm-A    | ✅     | ✅        |
| Chan-Open-Confirm-P    | ❌     | ❌        |
|                        |        |           |
| Chan-Close-Init        | ✅     | ✅        |
| Chan-Close-Confirm-A   | ✅     | ✅        |
| Chan-Close-Confirm-P   | ❌     | ❌        |
|                        |        |           |
| FT-Transfer            | ✅     | ✅        |
| Packet-Recv-A          | ✅     | ✅        |
| Packet-Recv-P          | ✅     | ✅        |
| Packet-Timeout-A       | ✅     | ✅        |
| Packet-Timeout-P       | ✅     | ✅        |
| Packet-TimeoutClose-A  | ✅     | ✅        |
| Packet-TimeoutClose-P  | ✅     | ✅        |
|                        |        |           |
| Upgrade-Plan-Proposal  | ❌     | ✅        |
| Cl-Unfreeze-Proposal   | ❌     | ❌        |
| Cl-Misbehavior         | ❌     | ❌        |
|                        |        |           |
| Cl-Non-Tendermint      | ❌     | ✅        |
| Chain-Non-Cosmos       | ❌     | ✅        |
|                        |        |           |
| Mgmt-Static            | ✅     | ✅        |
| Mgmt-Dynamic           | ❌     | ✅        |


__Legend__:

| Term              | Description                                                                                      |
| -----             | -----------                                                                                      |
| ❌                | feature not supported                                                                            |
| ✅                | feature is supported                                                                             |
| `Chain`           | chain related                                                                                    |
| `Cl`              | client related                                                                                   |
| `Conn`            | connection related                                                                               |
| `Chan`            | channel related                                                                                  |
| `..-Handshake-..` | can execute all transactions required to finish a handshake from a single command                |
| `..-<msg>-A`      | building and sending `msg` from a command that scans chain state                                 |
| `..-<msg>-P`      | building and sending `msg` from IBC event, doesn't apply to `..-Init` and `FT-Transfer` features |


## Feature Reference List

[WIP - add more detail]

- Restart: replays any IBC events that happened before restart
- Multiple-Paths: relays on multiple paths concurrently

- Cl-Tendermint-Create: tendermint light client creation
- Cl-Tendermint-Update: tendermint light client update
- Cl-Tendermint-Upgrade: tendermint light client upgrade

- Conn-Handshake-A
- Conn-Handshake-P
- Chan-Handshake-A
- Chan-Handshake-P

- Conn-Open-Init
- Conn-Open-Try-A
- Conn-Open-Try-P
- Conn-Open-Ack-A
- Conn-Open-Ack-P
- Conn-Open-Confirm-A
- Conn-Open-Confirm-P

- Chan-Open-Init
- Chan-Open-Try-A
- Chan-Open-Try-P
- Chan-Open-Ack-A
- Chan-Open-Ack-P
- Chan-Open-Confirm-A
- Chan-Open-Confirm-P
- Chan-Close-Init
- Chan-Close-Confirm-A
- Chan-Close-Confirm-P

- FT-Transfer: can submit an ICS-20 fungible token transfer message
- Packet-Recv-A
- Packet-Recv-P
- Packet-Timeout-A
- Packet-Timeout-P
- Packet-TimeoutClose-A
- Packet-TimeoutClose-P

- Upgrade-Plan-Proposal: submit `UpgradePlan` proposals for an IBC breaking upgrades
- Cl-Unfreeze-Proposal: submit IBC client unfreezing proposals
- Cl-Misbehavior: monitors and submits IBC client misbehavior

- Cl-Non-Tendermint: supports non-tendermint IBC light clients
- Chain-Non-Cosmos: supports non-cosmos-SDK chains

- Management-Static: provides means for configuration prior to being started
- Management-Dynamic: provides means for configuration and monitorig during runtime

