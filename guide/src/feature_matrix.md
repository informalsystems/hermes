# Feature Matrix
This section gives more details about the features and implementation status for the Hermes Rust and the [Cosmos Go relayer][cosmos-go-relayer].

__Legend__:

| Term              | Description                                                                                      |
| -----             | -----------                                                                                      |
| ❌                | feature not supported                                                                            |
| ✅                | feature is supported                                                                             |
| `Chain`           | chain related                                                                                    |
| `Cl`              | client related                                                                                   |
| `Conn`            | connection related                                                                               |
| `Chan`            | channel related                                                                                  |
| `..Handshake..`   | can execute all transactions required to finish a handshake from a single command                |
| `..-<msg>-A`      | building and sending `msg` from a command that scans chain state                                 |
| `..-<msg>-P`      | building and sending `msg` from IBC event, doesn't apply to `..-Init` and `FT-Transfer` features |
>>>>>>> Stashed changes

__Feature comparison between Hermes and the Go relayer__ 

| Features \      Status | Hermes | Cosmos Go | Feature Details  |
| ---------------------- | :----: | :-------: |:-------|
| Restart                | ❌     | ✅        | replays any IBC events that happened before restart
| Multiple-Paths         | ❌     | ✅        | relays on multiple paths concurrently
|                        |        |           |
| Cl-Tendermint-Create   | ✅     | ✅        | tendermint light client creation
| Cl-Tendermint-Update   | ✅     | ✅        | tendermint light client update
| Cl-Tendermint-Upgrade  | ❌     | ✅        | tendermint light client upgrade
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
| FT-Transfer            | ✅     | ✅        | can submit an ICS-20 fungible token transfer message
| Packet-Recv-A          | ✅     | ✅        |
| Packet-Recv-P          | ✅     | ✅        |
| Packet-Timeout-A       | ✅     | ✅        |
| Packet-Timeout-P       | ✅     | ✅        |
| Packet-TimeoutClose-A  | ✅     | ❓        |
| Packet-TimeoutClose-P  | ✅     | ❓        |
|                        |        |           |
| Upgrade-Plan-Proposal  | ❌     | ✅        | submit `UpgradePlan` proposals for IBC breaking upgrades
| Cl-Unfreeze-Proposal   | ❌     | ❌        | submit IBC client unfreezing proposals
| Cl-Misbehavior         | ❌     | ❌        | monitors and submits IBC client misbehavior
|                        |        |           |
| Cl-Non-Tendermint      | ❌     | ❌        | supports non-tendermint IBC light clients
| Chain-Non-Cosmos       | ❌     | ❌        | supports non-cosmos-SDK chains
|                        |        |           |
| Mgmt-Static            | ✅     | ✅        | provides means for configuration prior to being started
| Mgmt-Dynamic           | ❌     | ❌        | provides means for configuration and monitorig during runtime



[cosmos-go-relayer]: https://github.com/cosmos/relayer