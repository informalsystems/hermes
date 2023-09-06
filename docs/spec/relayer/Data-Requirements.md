# Hermes IBC Relayer Data Requirements

## Table of Contents

- [CometBFT RPC](#cometbft-rpc)
  * [`/health`](#health)
  * [`/consensus_params`](#consensus_params)
  * [`/status`](#status)
  * [`/header`](#header)
  * [`/latest_commit`, `/commit`, `/validators`](#latest_commit-commit-validators)
  * [`/abci_query`](#abci_query)
  * [`/tx_search`](#tx_search)
  * [`/block_search`](#block_search)
  * [`/block_results`](#block_results)
  * [`/broadcast_tx_sync`](#broadcast_tx_sync)
  * [`/broadcast_evidence`](#broadcast_evidence)
- [CometBFT WebSocket](#cometbft-websocket)
- [CometBFT gRPC](#cometbft-grpc)

## CometBFT RPC

The following endpoints (or equivalent) are necessary for operating the relayer.
They are ordered from lowest to highest impact roughly, i.e., the first endpoint in the list is the least important and least frequently required.

### `/health`

- Needed for basic check to assess node health.
- Not needed for IBC relaying strictly speaking.
- Only used once, at relayer startup during health check.

### `/consensus_params`

- Needed for basic check to validate relayer configuration.
- Specifically, used for fetching `consensus_params.block.max_bytes` and `consensus_params.block.max_gas` parameters.
- Not needed for IBC relaying strictly speaking.
- Only used once, at relayer startup during health check.
- **Response fields used:**
    - `block.max_bytes`
    - `block.max_gas`

### `/status`

Used in two situations:

1. At relayer startup to fetch `node_info.id`, for initializing the light client component.
   - Also at startup to fetch `node_info.other.tx_index`, during health check.
   - Also at startup to fetch `node_info.network`, i.e., the network identifier, during health check.
   - Also at startup to assert that `sync_info.catching_up` is false, during health check.
2. To fetch `sync_info.latest_block_time` and `sync_info.latest_block_height` and `sync_info.catching_up` used in many methods, often alongside `node_info.network`, for example:
  a. As a dependency, because the `latest_block_height` parameter is necessary in calling the `/consensus_params` RPC, during health check.
  b. Needed in channel handshake (open try, ack, confirm; close confirm).
  c. In connection handshake (open try, ack, confirm), for both the source chain (to update client), and destination chain (to construct proofs). Note: It seems like we bombard the node with /status queries, but most of the queries hit the Hermes in-process cache.
  d. For updating clients during everyday IBC relaying. In case there is non-zero connection delay, we again bombard the node with /status queries.

### `/header`

- To pull the header in the latest block that the application committed, in order to compute the latest app height and app timestamp
- To get the a block header at a specific/latest height and extract the consensus state from it

### `/latest_commit`, `/commit`, `/validators`

- For the CometBFT light client operations, mainly used to build `LightBlocks` and verify them

### `/abci_query`

Used in two situations:
1. To obtain the client upgraded state, while the relayer is handling chain upgrades.
2. To construct proofs for every IBC message relayed.
  - This method is used very frequently and is critical for IBC relaying!
  - Does not seem to impact performance of relaying, i.e., this method does not seem particularly slow or problematic.

> Note: We use `/header` and `/abci_query` together (see https://github.com/tendermint/tendermint/issues/8248)

### `/tx_search`

In four situations:

1. Query to obtain transaction events, for confirming if packets are committed to the blockchain.
      - Not needed on the critical path of packet relaying. Used very often as part of packet confirmation.
      - Pattern: `tx.hash == XYZ`
2. Query to obtain client update events: (a) for the misbehavior detection task, and (b) for relaying packets on connections that have non-zero delay.
      - Used rarely in practice because all connections have 0 delay and often misbehavior detection is disabled.
      - Pattern: `update_client.client_id == 07-tendermint-X && update_client.consensus_height == X-Y`
3. Query for the success/error status of a transaction immediately after it was broadcast.
      - Used rarely: at bootstrap (to register counterparty payee address for fees) or when transactions need to be sent sequentially (eg workaround for priority mempool or corner cases to avoid sequence mismatch).
      - Pattern: `tx.hash == XYZ`
4. Query to obtain packet events that occurred at or before a specified height. Required because application state does not store the full packet data which is needed to build and relay the packet messages.
      - Pattern: `send_packet.packet_src_channel == X && send_packet.packet_src_port == X && send_packet.packet_dst_channel == X && send_packet.packet_dst_port == X && send_packet.packet_sequence == X`. Also for `write_acknowledgement` packet events.
      - Used relatively often, on start and then for every `z` blocks, where `clear_interval = z` (default `z = 100`).

**Response fields used**:
- `txs[].height`
- `txs[].tx_result.events`

### `/block_search`

The use-case is similar to point (4) from `/tx_search`. We use it to obtain packet events from block data, used relatively often, on start and then for every `z` blocks, where `clear_interval = z` (default `z = 100`).

#### Pattern
`send_packet.packet_src_channel == X && send_packet.packet_src_port == X && send_packet.packet_dst_channel == X && send_packet.packet_dst_port == X && send_packet.packet_sequence == X`.
Also for `write_acknowledgement` packet events.

**Note:** Always used in conjunction with `block_results`.
 The `block_search` is used to determine the `Block` that included a packet event. Then `block_search` is used with the block's height to extract the packet event. 

**Response fields used:**
- `blocks[].block.header.height`

### `/block_results`

Used in two situations ([diagram for reference](https://app.excalidraw.com/l/4XqkU6POmGI/9jbKsT6mHxf)):

1. Similar to point (4) from `/tx_search`: Used In conjunction with `block_search` and `tx_search` for periodic packet clearing.
    - Pattern: `/block_results?height=X` where X is a specific height, obtained with `block_results`, where a block has relevant packet events. Only `begin_block_events` and `end_block_events` are used in this case. Since CometBFT 0.38, these fields are replaced with `finalize_block_events`.
2. For CLIs `tx packet-recv` and `tx packet-ack` when the user passes the flag `--packet-data-query-height=X`.

**Response fields used:**
- `begin_block_events` (before CometBFT 0.38)
- `end_block_events` (before CometBFT 0.38)
- `finalize_block_events` (since CometBFT 0.38)
- `height`
- `tx_results[].events`

### `/broadcast_tx_sync`

- For submitting transactions into the mempool.

__Note__: The above list is partly inspired from [cosmos-sdk/#11012](https://github.com/cosmos/cosmos-sdk/issues/11012) but extended and updated.

### `/broadcast_evidence`

- For submitting evidence of a chain misbehaving

## CometBFT WebSocket

The relayer connects to the node's CometBFT websocket interface and subscribes to the following events:
- for events that have type `NewBlock`
- for events that have type `Tx` and are IBC client, connection, and channel, i.e.,
    - `message.module == "ibc_client"`
    - `message.module == "ibc_connection"`
    - `message.module == "ibc_channel"`
- eventually the relayer should avoid using the non-standard, ibc-go specific `message.module` key and instead use the following queries:
    - `EXISTS create_client`
    - `EXISTS update_client`
    - `EXISTS client_misbehaviour`
    - `EXISTS connection_open_init`
    - `EXISTS connection_open_try`
    - `EXISTS connection_open_ack`
    - `EXISTS connection_open_confirm`
    - `EXISTS channel_open_init`
    - `EXISTS channel_open_try`
    - `EXISTS channel_open_ack`
    - `EXISTS channel_open_confirm`
    - `EXISTS channel_close_init`
    - `EXISTS channel_close_confirm`
    - `EXISTS channel_upgrade_init`
    - `EXISTS channel_upgrade_try`
    - `EXISTS channel_upgrade_ack`
    - `EXISTS channel_upgrade_confirm`
    - `EXISTS send_packet`
    - `EXISTS recv_packet`
    - `EXISTS write_acknowledgement`
    - `EXISTS acknowledge_packet`
    - `EXISTS timeout_packet`

## CometBFT gRPC

The following are the gRPC endpoints that Hermes makes use of, listed in rough priority from most used to least used. 

### `ibc.core.channel.v1.QueryClient`

Queries for channel-associated data, such as packet commitments, unreceived packets, all channels associated with a given connection, etc.

The requests that Hermes makes to this endpoint are:

- QueryChannelClientStateRequest
- QueryChannelsRequest
- QueryConnectionChannelsRequest
- QueryNextSequenceReceiveRequest
- QueryPacketAcknowledgementsRequest
- QueryPacketCommitmentsRequest
- QueryUnreceivedAcksRequest
- QueryUnreceivedPacketsRequest

### `ibc.core.client.v1.QueryClient`

Queries the client in order to fetch client and consensus states.

### `ibc.core.connection.v1.QueryClient`

Queries the connection in order to fetch connection data and connected clients.

### `interchain_security.ccv.consumer.v1.QueryParams`

Queries a CCV Consumer chain to fetch its staking parameters, notably its unbonding period and the number of historical entries that the chain keeps.

### `cosmos.staking.v1beta1.QueryParams`

Queries a Cosmos chain to fetch its staking parameters, most notably the chain's unbonding period.

### `cosmos.base.node.v1beta1.ServiceClient`

Queries a Cosmos full node in order to fetch its configuration parameters.