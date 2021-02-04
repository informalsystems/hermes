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
| `.._Handshake_..`   | can execute all transactions required to finish a handshake from a single command                |
| `.._<msg>_A`      | building and sending `msg` from a command that scans chain state                                 |
| `.._<msg>_P`      | building and sending `msg` from IBC event; doesn't apply to `.._Init` and `FT_Transfer` features |

__Feature comparison between Hermes and the Go relayer__ 

| Features \      Status | Hermes | Cosmos Go | Feature Details  |
| ---------------------- | :---: | :----: |:-------|
| Restart                | ❌    | ✅     | replays any IBC events that happened before restart
| Multiple_Paths         | ❌    | ✅     | relays on multiple paths concurrently
| Chan_Unordered         | ✅    | ✅     |
| Chan_Ordered           | ❌    | ❓     |
|                        |       |        |
| Cl_Tendermint_Create   | ✅    | ✅     | tendermint light client creation
| Cl_Tendermint_Update   | ✅    | ✅     | tendermint light client update
| Cl_Tendermint_Upgrade  | ❌    | ✅     | tendermint light client upgrade
|                        |       |        |
| Conn_Handshake_A       | ✅    | ✅     |
| Conn_Handshake_P       | ❌    | ❌     |
| Chan_Handshake_A       | ✅    | ✅     |
| Chan_Handshake_P       | ❌    | ❌     |
|                        |       |        |
| Conn_Open_Init         | ✅    | ✅     |
| Conn_Open_Try_A        | ✅    | ✅     |
| Conn_Open_Try_P        | ❌    | ❌     |
| Conn_Open_Ack_A        | ✅    | ✅     |
| Conn_Open_Ack_P        | ❌    | ❌     |
| Conn_Open_Confirm_A    | ✅    | ✅     |
| Conn_Open_Confirm_P    | ❌    | ❌     |
|                        |       |        |
| Chan_Open_Init         | ✅    | ✅     |
| Chan_Open_Try_A        | ✅    | ✅     |
| Chan_Open_Try_P        | ❌    | ❌     |
| Chan_Open_Ack_A        | ✅    | ✅     |
| Chan_Open_Ack_P        | ❌    | ❌     |
| Chan_Open_Confirm_A    | ✅    | ✅     |
| Chan_Open_Confirm_P    | ❌    | ❌     |
|                        |       |        |
| Chan_Close_Init        | ✅    | ✅     |
| Chan_Close_Confirm_A   | ✅    | ✅     |
| Chan_Close_Confirm_P   | ❌    | ❌     |
|                        |       |        |
| FT_Transfer            | ✅    | ✅     | can submit an ICS-20 fungible token transfer message
| Packet_Recv_A          | ✅    | ✅     |
| Packet_Recv_P          | ✅    | ✅     |
| Packet_Timeout_A       | ✅    | ✅     |
| Packet_Timeout_P       | ✅    | ✅     |
| Packet_TimeoutClose_A  | ✅    | ❓     |
| Packet_TimeoutClose_P  | ✅    | ❓     |
|                        |       |        |
| Upgrade_Plan_Proposal  | ❌    | ✅     | submit `UpgradePlan` proposals for IBC breaking upgrades
| Cl_Unfreeze_Proposal   | ❌    | ❌     | submit IBC client unfreezing proposals
| Cl_Misbehavior         | ❌    | ❌     | monitors and submits IBC client misbehavior
|                        |       |        |
| Cl_Non_Tendermint      | ❌    | ❌     | supports non tendermint IBC light clients
| Chain_Non_Cosmos       | ❌    | ❌     | supports non cosmos-SDK chains
|                        |       |        |
| Mgmt_Static            | ✅    | ✅     | provides means for configuration prior to being started
| Mgmt_Dynamic           | ❌    | ❌     | provides means for configuration and monitoring during runtime


[cosmos-go-relayer]: https://github.com/cosmos/relayer