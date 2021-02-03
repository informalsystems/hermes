# Feature Matrix, Implementation Comparison

This section gives more details on some of the features and implementation status for the Hermes Rust and the Cosoms Go relayers.

## Feature Matrix
| Features \ Impl Status | Hermes | Cosmos Go  |
| ----- |:-----| :-----|
| Restart | X | V |
| Multiple-Paths | X | V |
| | | |
| Cl-Tendermint-Create | V | V |
| Cl-Tendermint-Update | V | V |
| Cl-Tendermint-Upgrade | X | V |
| | | |
| Conn-Handshake-A | V | V |
| Conn-Handshake-P | X | X |
| Chan-Handshake-A | V | V |
| Chan-Handshake-P | X | X |
| | | |
| Conn-Open-Init | V | V |
| Conn-Open-Try-A | V | V |
| Conn-Open-Try-P | X | X |
| Conn-Open-Ack-A | V | V |
| Conn-Open-Ack-P | X | X |
| Conn-Open-Confirm-A | V | V |
| Conn-Open-Confirm-P | X | X |
| | | |
| Chan-Open-Init | V | V |
| Chan-Open-Try-A | V | V |
| Chan-Open-Try-P | X | X |
| Chan-Open-Ack-A | V | V |
| Chan-Open-Ack-P | X | X |
| Chan-Open-Confirm-A | V | V |
| Chan-Open-Confirm-P | X | X |
| | | |
| Chan-Close-Init | V | V |
| Chan-Close-Confirm-A | V | V |
| Chan-Close-Confirm-P | X | X |
| | | |
| FT-Transfer | V | V |
| Packet-Recv-A | V | V |
| Packet-Recv-P | V | V |
| Packet-Timeout-A | V | V |
| Packet-Timeout-P | V | V |
| Packet-TimeoutClose-A | V | V |
| Packet-TimeoutClose-P | V | V |
| | | |
| Upgrade-Plan-Proposal | X | V |
| Cl-Unfreeze-Proposal  | X | X |
| Cl-Misbehavior | X | X |
| | | |
| Cl-Non-Tendermint | X | V |
| Chain-Non-Cosmos | X | V |
| | | |
| Mgmt-Static | Y | Y |
| Mgmt-Dynamic | X | V |
| | | |
| | | |


## Feature Reference List
__Legend__:

- `X` - feature not supported
- `V` - feature is supported
- `Chain` - chain related
- `Cl` - client related
- `Conn` - connection related
- `Chan` - channel related
- `..-Handshake-..` - can execute all transactions required to finish a handshake from a single command
- `..-<msg>-A` - building and sending `msg` from a command that scans chain state
- `..-<msg>-P` - building and sending `msg` from IBC event, doesn't apply to `..-Init` and `FT-Transfer` features


__Features__:

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

