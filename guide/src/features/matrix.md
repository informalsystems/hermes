# Feature Matrix
This section gives more details about the features and implementation status 
of Hermes in comparison with the [cosmos-go-relayer].

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

__Feature comparison between Hermes and the Go relayer__ 

| Features \      Status | Hermes | Cosmos Go | Feature Details  |
| ---------------------- | :---: | :----: |:-------|
| Restart                | ✅    | ✅     | replays any IBC events that happened before restart
| Multiple_Paths         | ✅    | ✅     | relays on multiple paths concurrently
|                        |       |        |
| Connection Delay       | ✅    | ❌     | 
| Cl_Misbehavior         | ✅    | ❌     | monitors and submits IBC client misbehavior
| Cl_Refresh             | ✅    | ❌     | periodically refresh an on-chain client to prevent expiration
| Packet Delay           | ✅    | ❌     | 
|                        |       |        |
| Chan_Unordered         | ✅    | ✅     |
| Chan_Ordered           | ✅    | ❓     |
|                        |       |        |
| Cl_Tendermint_Create   | ✅    | ✅     | tendermint light client creation
| Cl_Tendermint_Update   | ✅    | ✅     | tendermint light client update
| Cl_Tendermint_Upgrade  | ✅    | ✅     | tendermint light client upgrade
|                        |       |        |
| Conn_Open_Handshake_A  | ✅    | ✅     |
| Conn_Open_Handshake_P  | ✅    | ❌     |
|                        |       |        |
| Chan_Open_Handshake_A  | ✅    | ✅     |
| Chan_Open_Handshake_P  | ✅    | ❌     |
| Chan_Open_Handshake_Optimistic  | ❌    | ❌     | open a channel on a non-Open connection
|                        |       |        |
| Chan_Close_Handshake_P | ✅    | ✅     | 
| Chan_Close_Handshake_A | ✅    | ❌     |
|                        |       |        |
| FT_Transfer            | ✅    | ✅     | can submit an ICS-20 fungible token transfer message
| ICA_Relay               | ✅    | ❌     | can relay ICS-27 Interchain account packets
| Packet_Recv_A          | ✅    | ✅     |
| Packet_Recv_P          | ✅    | ✅     |
| Packet_Timeout_A       | ✅    | ✅     |
| Packet_Timeout_P       | ✅    | ✅     |
| Packet_TimeoutClose_A  | ✅    | ❓     |
| Packet_TimeoutClose_P  | ✅    | ❓     |
| Packet_Optimistic      | ❌    | ❓     | relay packets over non-Open channels
|                        |       |        |
| Cl_Non_Tendermint      | ❌    | ❌     | supports non tendermint IBC light clients
| Chain_Non_Cosmos       | ❌    | ❌     | supports non cosmos-SDK chains
|                        |       |        |
| Cfg_Static            | ✅    | ✅     | provides means for configuration prior to being started
| Cfg_Dynamic           | ❌    | ❌     | provides means for configuration and monitoring during runtime
| Cfg_Download_Config   | ❌    | ✅     | provides means for downloading recommended configuration 
| Cfg_Edit_Config       | ❌    | ✅     | provides means for editing the configuration from the CLI 
| Cfg_Validation        | ✅    | ✅     | provides means to validate the current configuration 
| Telemetry             | ✅    | ❌     | telemetry server to collect metrics 
| REST API              | ✅    | ❌     | REST API to interact with the relayer 



[cosmos-go-relayer]: https://github.com/cosmos/relayer
