# Hermes versus App/SDK/Tendermint Configuration

This table summarizes the different configuration parameter combinations that may cause Hermes to raise errors. It gives some information on the failure type and refers to the relevant section of the guide for more information.
Following notations are used:

- `tendermint.<parameter>`: 
  - `tendermint` refers to the Tendermint configuration file `config.toml`
  - `<parameter>` refers to the parameter in this file.
- `app.<parameter>`:
  - `app` refers to the application configuration file `app.toml`
  - `<parameter>` refers to the parameter in this file.
- `genesis.<parameter>`:
- `genesis` refers to the application configuration file `genesis.json`
- `<parameter>` refers to the parameter in this file.



__Hermes vs other configuration parameters that may cause Hermes failures__

| Hermes                                                                                                                                                                                                                                                                                                                     | Other                                                                                                            | Details                                                               |
|----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------------------------------|-----------------------------------------------------------------------|
| `sequential_batch_tx = false`                                                                                                                                                                                                                                                                                              | `tendermint.recheck = false`                                                                                     | [`Mismatch`<br/>`(expected < got)`](#recheck)                         |
|                                                                                                                                                                                                                                                                                                                            |                                                                                                                  |                                                                       |
| `gas_price = x`                                                                                                                                                                                                                                                                                                            | `app.minimum-gas-prices = y, `<br/>`with x < y`                                                                  | [`Insufficient fees`](#minimum-gas-price)                             |
|                                                                                                                                                                                                                                                                                                                            |                                                                                                                  |                                                                       |
| `gas_price = x` <br/> `gas_multipler = 1.0`                                                                                                                                                                                                                                                                                | `app.minimum-gas-prices = x`                                                                                     | [`Out of gas`](#out-of-gas)                                           |
|                                                                                                                                                                                                                                                                                                                            |                                                                                                                  |                                                                       |
| `max_tx_size = x`                                                                                                                                                                                                                                                                                                          | `tendermint.max_tx_bytes = y,`<br/>`with x < y`                                                                  | [`Tx too large`](#maximum-tx-size)                                    |
|                                                                                                                                                                                                                                                                                                                            |                                                                                                                  |                                                                       |
|                                                                                                                                                                                                                                                                                                                            | `07-tendermint not in`<br/>`genesis.app_state`<br/>`.ibc.client_genesis.params`<br/>`.allowed_clients`           | [`Client not `<br/>`allowed`<br/>`(07-tendermint)`](#allowed-clients) |
|                                                                                                                                                                                                                                                                                                                            |                                                                                                                  |                                                                       |
| `during connection creation`                                                                                                                                                                                                                                                                                               | `genesis.app_state`<br/>`.staking.params`<br/>`.historical_entries  = 0`                                         | [`No historical info`](#historical-entries)                           |
|                                                                                                                                                                                                                                                                                                                            |                                                                                                                  |                                                                       |
| `ref_chain.clock_drift +`<br/>`tgt_chain.clock_drift +`<br/>`tgt_chain.max_block_time`<br/>`= x`                                                                                                                                                                                                                           | `tendermint.consensus.* => y block time,`<br/>`with x < y`                                                       | [`Header in the future` ](#header-in-the-future)                      |
|                                                                                                                                                                                                                                                                                                                            |                                                                                                                  |                                                                       |
| `max_block_delay = x`                                                                                                                                                                                                                                                                                                      | `genesis.app_state`<br/>`.ibc.connection_genesis.params`<br/>`.max_expected_time_per_block = y`<br/>`with x < y` | [`Block delay not reached`](#block-delay-not-reached)                 |
|                                                                                                                                                                                                                                                                                                                            |                                                                                                                  |                                                                       |
| `key_name = <wallet_name>`                                                                                                                                                                                                                                                                                                 |                                                                                                                  | [`Insufficient funds`](#insufficient-funds) |
|| `app.pruning = "custom",`<br/>`app.pruning-keep-recent= w,`<br/>`app.pruning-keep-every = x,`<br/>`app.pruning-interval = y,`<br/>`app.min-retain-blocks = z,`<br/>`genesis.consensus_params.evidence.max_age_num_blocks = e,`<br/>`genesis.consensus_params.evidence.max_age_duration = d` | [`Uncleared packets`](#uncleared-pending-packets)                                                                       |


## Recheck
When relaying packets, Hermes may send up multiple transactions to the full node's mempool. Hermes uses the  `broadcast_tx_sync` RPC which does some basic verification and then returns the Tx hash back. 

Unless configured with `sequential_batch_tx = true`, Hermes does not wait for a transaction to be included in a block before sending the next transaction. For this to be possible, Hermes keeps track of the account sequence number locally, incrementing it after each succesfull `broadcast_tx_sync` RPC.

During peak periods, it is possible that not all Tx-es in the mempool are included in a block. In order for new transactions to be accepted along with the pending Tx-es, the full node must be configured with `recheck = true`. Otherwise, Hermes may get the following error:
```
2022-10-25T13:52:51.369822Z  WARN ThreadId(18) send_messages_and_wait_commit
  {chain=ibc-0 tracking_id=ft-transfer}:send_tx_with_account_sequence_retry{chain=ibc-0 account.sequence=88}: 
    failed to broadcast tx because of a mismatched account sequence number, refreshing account sequence number and 
      retrying once response=Response { code: Err(32), data: Data([]), log: Log("account sequence mismatch, 
        expected 69, got 88: incorrect account sequence"), 
      hash: transaction::Hash(DFC53B04CE095CD045E4E89D7CEB095BF977B876FD8D3FB1A7F0AC288B58B9C4) }
```

### Fix
Ensure that the full node is configured with `recheck = true`.
This ensures that the mempool rechecks the Tx-es left in the mempool before accepting new incoming transactions, therefore maintaining the order of transactions.

## Minimum Gas Price
Hermes sends transactions using the `gas_price` parameter from the chain section in the Hermes `config.toml` configuration file. The full node will not accept any transactions with a gas price smaller than what is configured for the applications (`app.minimum-gas-prices`) and Hermes will log an `insufficient fees` error:

```
2022-10-27T12:45:07.820543Z ERROR ThreadId(18) send_messages_and_wait_commit{chain=ibc-0 tracking_id=ft-transfer}:
  send_tx_with_account_sequence_retry{chain=ibc-0 account.sequence=48}: failed to broadcast tx with unrecoverable error
     response=Response { code: Err(13), data: Data([]), log: Log("insufficient fees; got: 99stake required: 198stake: insufficient fee"), 
       hash: transaction::Hash(AFB9FE23DE9108D349B8679561D7F00DF00863749D7827C3972DFB391CF8E526) } 
         diagnostic=the price configuration for this chain may be too low! please check the `gas_price.price` Hermes config.toml
ERROR transfer error: tx response event consists of an error: check_tx (broadcast_tx_sync) on chain ibc-0 for 
  Tx hash AFB9FE23DE9108D349B8679561D7F00DF00863749D7827C3972DFB391CF8E526 reports error: 
    vcode=Err(13), log=Log("insufficient fees; got: 99stake required: 198stake: insufficient fee")
``` 

### Fix
Ensure that the `gas_price.price` parameter in the chain section of the Hermes `config.toml` configuration file is greater than or equal to the `app.minimum-gas-prices`.

## Out of Gas
Before Hermes sends a transaction, it estimates how much gas the transaction will require by calling the `SimulateTx()` gRPC. This returns the amount of gas that the Tx requires given the application state at the time of the call. It is possible that by the time the transaction is sent and checked by the application, the amount of gas required has increased. To help alleviate this, the gas estimation is adjusted upward by multiplying it by the `gas_multiplier` parameter: `gas_multiplier * simulated_gas`.

If the adjusted amount of gas ends up still being not enough for the transaction to be successfully submitted, e.g., the `gas_multiplier` parameter is set to `1.0` such that no adjustment is actually performed, Hermes returns the following error:
```
ERROR transfer error: tx response event consists of an error: deliver_tx for 496835FF5A2F73F38ADA416506F7F1143BBD570E77217DC309CAD979924F0E70 reports error: code=Err(11), log=Log("out of gas in location: WriteFlat; gasWanted: 990000, gasUsed: 990724: out of gas")
```

### Fix
Ensure that the `gas_multiplier` parameter in the chain section of the Hermes `config.toml` configuration file is configured such that it allows some increase over the simulated gas. A good value is for example `1.1`.

## Maximum Tx Size
When Hermes relays packets or handshake messages, it will build multi-message Tx-es with up to `max_num_msgs` number of messages or up to a Tx size of `max_tx_size` bytes. The full node accepts only Tx-es with size up to the `max_tx_bytes` parameter in its `config.toml`. If a Tx is too large, the full node rejects them with the following error:

```
2022-10-27T13:59:43.650251Z ERROR ThreadId(18) send_messages_and_wait_commit{chain=ibc-0 tracking_id=ft-transfer}:send_tx_with_account_sequence_retry{chain=ibc-0 account.sequence=159}: gas estimation failed or encountered another unrecoverable error error=RPC error to endpoint http://127.0.0.1:26657/: response error: Internal error: Tx too large. Max size is 500, but got 615 (code: -32603)
ERROR transfer error: failed while submitting the Transfer message to chain ibc-0: RPC error to endpoint http://127.0.0.1:26657/: response error: Internal error: Tx too large. Max size is 500, but got 615 (code: -32603)
```
### Fix
Ensure that the `max_tx_size` parameter configured for Hermes is smaller than the `max_tx_bytes` parameter configured for the full node.

## Allowed Clients
The SDK chain genesis file contains a list of allowed clients that can be created on a chain. If the chain is configured with `genesis.app_state.ibc.client_genesis.allowed_clients` that doesn't include `07-tendermint`, then the chain will not allow tendermint IBC clients to be created and Hermes cannot open an IBC connection with this chain. When attempting to create a client in this scenario, Hermes will get the following error:

```
2022-10-27T14:48:04.632320Z ERROR ThreadId(35) send_messages_and_wait_commit{chain=ibc-0 tracking_id=create client}:send_tx_with_account_sequence_retry{chain=ibc-0 account.sequence=0}:estimate_gas: failed to simulate tx. propagating error to caller: gRPC call failed with status: status: Unknown, message: "failed to execute message; message index: 0: client state type 07-tendermint is not registered in the allowlist: invalid client type [cosmos/ibc-go/v3@v3.0.0/modules/core/02-client/keeper/client.go:22] With gas wanted: '0' and gas used: '64671' ", details: [], metadata: MetadataMap { headers: {"content-type": "application/grpc", "x-cosmos-block-height": "9"} }
```
### Fix
Ensure that the `genesis.app_state.ibc.client_genesis.allowed_clients` parameter in the chain genesis file includes `07-tendermint`.

## Historical Entries
The presence of recent consensus states on a chain is required when processing some connection handshake messages, such as `MsgConnectionOpenTry` and `MsgConnectionOpenAck`. Such message types require proof verification that the counterparty chain has a valid client for this chain.
If the chain is configured with `genesis.app_state.staking.params.historical_entries = 0`, then the chain will not store historical consensus state information and Hermes cannot open IBC connections with this chain. It will report an error message which looks like this:

```
2022-10-27T14:54:51.076598Z ERROR ThreadId(18) send_messages_and_wait_commit{chain=ibc-0 tracking_id=ConnectionOpenAck}:send_tx_with_account_sequence_retry{chain=ibc-0 account.sequence=6}:estimate_gas: failed to simulate tx. propagating error to caller: gRPC call failed with status: status: Unknown, message: "failed to execute message; message index: 1: connection handshake open ack failed: self consensus state not found for height 0-88: no historical info found at height 88: not found [cosmos/ibc-go/v3@v3.0.0/modules/core/02-client/keeper/keeper.go:256] With gas wanted: '0' and gas used: '130807' ", details: [], metadata: MetadataMap { headers: {"content-type": "application/grpc", "x-cosmos-block-height": "90"} }
```

The chain genesis misconfiguration is caught when the health check runs, e.g. `hermes health-check`, `hermes start`. A warning message such as the following is printed:

```
2022-10-27T15:00:14.583244Z  WARN ThreadId(40) health_check{chain=ibc-0}: Health checkup for chain 'ibc-0' failed
2022-10-27T15:00:14.583308Z  WARN ThreadId(40) health_check{chain=ibc-0}:     Reason: staking module for chain 'ibc-0' does not maintain any historical entries (`historical_entries` staking params is set to 0)
2022-10-27T15:00:14.583343Z  WARN ThreadId(40) health_check{chain=ibc-0}:     Some Hermes features may not work in this mode!
```
### Fix
Ensure that the `genesis.app_state.staking.params.historical_entries` parameter in the chain genesis file is greater than 0. Ideal values are > 100.

## Maximum Block Time
There are two cases where misconfiguration of the maximum block time may cause Hermes to fail. They are described in the following sections.

### Header in the Future
When a client for chain `ref_chain` is created by Hermes on chain `tgt_chain`, its `max_clock_drift` is computed as:
`ref_chain.clock_drift + tgt_chain.clock_drift + tgt_chain.max_block_time`
Hermes may delay a client update with `header` for one block if it determines that sending it immediately would cause the chain to reject the update as being in the future.

Hermes sends the update in the case when `header.timestamp <= dst_timestamp + max_clock_drift`
where `dst_timestamp` is the last block time on the destination chain.
Otherwise, it waits for the next block and retries the update. If the check fails again, an error is returned:
```
2022-10-28T08:42:37.423739Z  WARN ThreadId(01) foreign_client.build_update_client_and_send{client=ibc-1->ibc-0:07-tendermint-0 target_query_height=latest height}:foreign_client.wait_and_build_update_client_with_trusted{client=ibc-1->ibc-0:07-tendermint-0 target_height=1-2182}:foreign_client.build_update_client_with_trusted{client=ibc-1->ibc-0:07-tendermint-0 target_height=1-2182}:foreign_client.wait_for_header_validation_delay{client=ibc-1->ibc-0:07-tendermint-0}: src header Timestamp(2022-10-28T08:42:35.600792Z) is after dst latest header Timestamp(2022-10-28T08:42:17.864603Z) + client state drift 3s,wait for next height on ibc-0
ERROR foreign client error: update header from ibc-1 with height 1-2182 and time Timestamp(2022-10-28T08:42:35.600792Z) is in the future compared with latest header on ibc-0 with height 0-4 and time Timestamp(2022-10-28T08:42:31.09872Z), adjusted with drift 3s
```

### Block Delay not Reached
An IBC packet sent to the channel end on a destination chain with `max_block_delay`, channel using a connection with `delay`, must be received:
- after the time delay: `delay` has elapsed relative to the block time that included the client update with the packet commitment root, and
- after the block delay: `delay / max_block_delay` blocks on the destination chain have been created since the client update with the packet commitment root.

The on-chain packet handler uses `genesis.app_state.ibc.connection_genesis.params.max_expected_time_per_block` (in nanoseconds) when computing the block delay.
Hermes uses its config `max_block_delay` to compute the block delay.
If `max_block_delay > genesis.app_state.ibc.connection_genesis.params.max_expected_time_per_block`, then Hermes may send a packet that is received too early on the destination chain, resulting in an error like the following:

```
ERROR link error: link failed with underlying error: gRPC call failed with status: status: Unknown, message: "failed to execute message; message index: 0: receive packet verification failed: couldn't verify counterparty packet commitment: failed packet commitment verification for client (07-tendermint-1): cannot verify packet until height: 0-54, current height: 0-46: packet-specified delay period has not been reached [cosmos/ibc-go/v3@v3.0.0/modules/light-clients/07-tendermint/types/client_state.go:536] With gas wanted: '0' and gas used: '78238' ", details: [], metadata: MetadataMap { headers: {"content-type": "application/grpc", "x-cosmos-block-height": "46"} }
```

### Fix
To avoid errors for both cases described above:
- ensure that the `max_block_delay` parameter in the Hermes configuration file is equal to the `max_expected_time_per_block` parameter in the chain genesis file:
```
genesis.app_state.ibc.connection_genesis.params.max_expected_time_per_block
```
- ensure that the genesis `max_expected_time_per_block` parameter is 2 or 3 times the average block time which can be estimates from the `tendermint.consensus.timeout*` parameters. An example of a good estimation is:
```
       tendermint.consensus.timeout_propose +
       tendermint.consensus.timeout_prevote +
       tendermint.consensus.timeout_precommit +
       tendermint.consensus.timeout_commit
```

## Insufficient Funds
If the wallet configured in Hermes' `config.toml` is empty or doesn't have enough funds, any transfer will result in the following error:

```
ERROR ThreadId(11) send_messages_and_wait_commit{chain=ibc-0 tracking_id=ft-transfer}:send_tx_with_account_sequence_retry{chain=ibc-0 account.sequence=25}:estimate_gas: failed to simulate tx. propagating error to caller: gRPC call failed with status: status: Unknown, message: "failed to execute message; message index: 0: 20stake is smaller than 108stake: insufficient funds [cosmos/cosmos-sdk@v0.46.3/x/bank/keeper/send.go:191] With gas wanted: '18446744073709551615' and gas used: '52497' ", details: [], metadata: MetadataMap { headers: {"content-type": "application/grpc", "x-cosmos-block-height": "377"} }
```

### Fix
In order to fix the error above, use one of the following two solutions:
- add enough funds to the wallet configured by `key_name` in Hermes' `config.toml`.
- change the wallet configured by `key_name` in Hermes' `config.toml` to a wallet which has enough funds.


## Uncleared Pending Packets
When Hermes starts, it retrieves the sequences for the unrelayed receive and acknowledgment packets from the application. Since only the packet commitments are stored in the application state, Hermes then queries tendermint for the IBC events with those sequence numbers and obtains the packet data from these events. The IBC events are retrieved from transaction and block indexes maintained by tendermint nodes.

In some cases these queries fail to obtain the packet data due to the fact that the state that contained those events has been pruned from the tendermint node. In this case Hermes will not be able to relay the packet. One example can be seen below. Hermes queries the application and finds `222` unreceived acknowledgment packets. Then it queries tendermint for the packet data but fails to find it (`pulled packet data for 0 events`). In this case the command returns zero relayed packets (`SUCCESS []`):

```
INFO ThreadId(01) relay_ack_packet_messages{src_chain=ibc-1 src_port=transfer src_channel=channel-0 dst_chain=ibc-0}: 222 unreceived acknowledgements found: 222
INFO ThreadId(01) relay_ack_packet_messages{src_chain=ibc-1 src_port=transfer src_channel=channel-0 dst_chain=ibc-0}: pulled packet data for 0 events; events.total=222 events.left=172
INFO ThreadId(01) relay_ack_packet_messages{src_chain=ibc-1 src_port=transfer src_channel=channel-0 dst_chain=ibc-0}: pulled packet data for 0 events; events.total=222 events.left=122
INFO ThreadId(01) relay_ack_packet_messages{src_chain=ibc-1 src_port=transfer src_channel=channel-0 dst_chain=ibc-0}: pulled packet data for 0 events; events.total=222 events.left=72
INFO ThreadId(01) relay_ack_packet_messages{src_chain=ibc-1 src_port=transfer src_channel=channel-0 dst_chain=ibc-0}: pulled packet data for 0 events; events.total=222 events.left=22
INFO ThreadId(01) relay_ack_packet_messages{src_chain=ibc-1 src_port=transfer src_channel=channel-0 dst_chain=ibc-0}: pulled packet data for 0 events; events.total=222 events.left=0
SUCCESS []
```

### State Pruning Background
In order to keep the disk storage low, Tendermint nodes may be configured to prune "old" data. 

#### Application State Pruning
The `app.toml` file defines a few parameters that control the application state pruning window:

```
pruning = <strategy>

# These are applied if and only if the pruning strategy is custom.
pruning-keep-recent = w
pruning-keep-every = x
pruning-interval = y
```

#### Tendermint State Pruning
The `app.toml` file also defines parameters to control the tendermint block pruning window:

```
min-retain-blocks = z
```

The evidence genesis parameters that also influence the actual size of the tendermint block pruning window are:
```
{
...
  "consensus_params": {
    "block": {
     ...
    },
    "evidence": {
      "max_age_num_blocks": b,
      "max_age_duration": d,
      ...
    },
```

These parameters are used to determine if a block (and associated state) should be pruned:
- a block with height `h` and time `t` is pruned if `h < max(z, b) && t < now - d`

Additional tendermint state may be maintained for state-sync purposes.

### Debug
The unrelayed packet sequences can be retrieved using the following command:

```
hermes query packet pending --chain <CHAIN_ID> --channel <CHANNEL_ID> --port <PORT_ID>
```
There are two RPC endpoints, `tx_search` and `block_search`, that can be used to check if the full node still has the event information.

For example, if a `send_packet` with sequence `6` has not been relayed and the packet was sent in a transaction, the `tx_search` RPC endpoint can be used:
```
http://localhost:26657/tx_search?query="send_packet.packet_sequence='6' AND send_packet.packet_src_channel='channel-0' AND send_packet.packet_src_port='transfer' AND send_packet.packet_dst_channel='channel-0' AND send_packet.packet_dst_port='transfer'"
```
If the packet was sent via begin or end blocker, the `block_search` RPC endpoint can be used:
```
http://localhost:26657/block_search?query="send_packet.packet_sequence='6' AND send_packet.packet_src_channel='channel-0' AND send_packet.packet_src_port='transfer' AND send_packet.packet_dst_channel='channel-0' AND send_packet.packet_dst_port='transfer'"
```

If these two queries return an empty result, the event information has been pruned from the full node.

### Fix
Depending on how old the missing events are:
- use an archive node, or
- adjust the pruning parameters of the full node to increase the pruning window and,
  - if state-sync is used, specify an initial state with a height that is smaller than the height at which the event occurred.
    - in order to find out the height of the missing events, use an archive node or a node with bigger pruning window and do the same queries as above
  - restart the node
