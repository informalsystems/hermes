# Telemetry

*Since version 0.4.0.*

To gain a better understanding of the status and activity of the relayer,
Hermes features a built-in telemetry service based on the [OpenTelemetry][opentelemetry] observability framework,
whose metrics can be exposed over HTTP for integration with the [Prometheus][prometheus] monitoring system.

The official Hermes builds for Linux and macOS come with telemetry support since version 0.4.0,
and can be [downloaded directly from the GitHub Releases][gh-releases] page.

[gh-releases]: https://github.com/informalsystems/ibc-rs/releases
[opentelemetry]: https://opentelemetry.io
[prometheus]: https://prometheus.io

## Configuration

The telemetry service is not active by default, and must be enabled in the relayer configuration:

```toml
[telemetry]
enabled = true
host    = '127.0.0.1'
port    = 3001
```

Please see the [relevant section in the *Configuration* page](./config.md#telemetry) for details about the configuration options.

## Metrics

The following table describes the metrics currently tracked by the telemetry service:

| Name                         | Description                                          | OpenTelemetry type  |
| ---------------------------- | ---------------------------------------------------- | ------------------- |
| `workers`                    | Number of workers per object                         | `i64` UpDownCounter |
| `ibc_client_updates`         | Number of client updates performed per client        | `u64` Counter       |
| `ibc_client_misbehaviours`   | Number of misbehaviours detected per client          | `u64` Counter       |
| `ibc_receive_packets`        | Number of receive packets relayed per channel        | `u64` Counter       |
| `ibc_acknowledgment_packets` | Number of acknowledgment packets relayed per channel | `u64` Counter       |
| `ibc_timeout_packets`        | Number of timeout packets relayed per channel        | `u64` Counter       |
| `wallet_balance`             | How much balance (coins) there is left in each wallet key that Hermes is using. | `u64` ValueRecorder       |
| `ws_events`                  | How many IBC events did Hermes receive via the websocket subscription, in total since starting up, per chain. | Counter       |
| `ws_reconnect`               | Number of times Hermes had to reconnect to the WebSocket endpoint                                                             | Counter       |
| `tx_latency_submitted`       | Latency for all transactions submitted to a chain (i.e., difference between the moment when Hermes received an event until the corresponding transaction(s) were submitted). | `u64` ValueRecorder       |
| `tx_latency_confirmed`       | Latency for all transactions confirmed by a chain (i.e., difference between the moment when Hermes received an event until the corresponding transaction(s) were confirmed). Requires `tx_confirmation = true`. | `u64` ValueRecorder       |
| `msg_num`                    | How many messages Hermes submitted to a specific chain. | `u64` Counter     |
| `queries`                    | Number of queries emitted by the relayer, per chain and query type | `u64` Counter |
| `query_cache_hits`           | Number of cache hits for queries emitted by the relayer, per chain and query type | `u64` Counter |
| `send_packet_count`          | Number of SendPacket relayed | `u64` Counter |
| `acknowledgement_count`      | Number of WriteAcknowledgement relayed               | `u64` Counter       |
| `cleared_count`              | Number of SendPacket relayed through ClearPendingPackets | `u64` Counter   |
| `oldest_sequence`            | The sequence number of the oldest pending SendPacket. If this value is 0, it means there are no pending SendPacket | `u64` ValueRecorder |
| `oldest_timestamp`           | The timestamp of the oldest sequence number in seconds | `u64` ValueRecorder |
| `client_update_message_count` | Number of MsgUpdateAnyClient relayed                | `u64` Counter       |

## Integration with Prometheus

With the settings , the telemetry service will be enabled and will serve the metrics using
the Prometheus encoder over HTTP at [`http://localhost:3001/metrics`](http://localhost:3001/metrics).

After starting Hermes with `hermes start`, and letting it run for a while to relay packets,
open [`http://localhost:3001/metrics`](http://localhost:3001/metrics) in a browser, you should
see Prometheus-encoded metrics.

For example, with two channels and after transferring some tokens between the chains:

```text
# HELP cache_hits Number of cache hits for queries emitted by the relayer, per chain and query type
# TYPE cache_hits counter
cache_hits{chain="ibc-0",query_type="query_channel"} 8
cache_hits{chain="ibc-0",query_type="query_client_state"} 15
cache_hits{chain="ibc-0",query_type="query_connection"} 11
cache_hits{chain="ibc-1",query_type="query_channel"} 9
cache_hits{chain="ibc-1",query_type="query_client_state"} 16
cache_hits{chain="ibc-1",query_type="query_connection"} 12
cache_hits{chain="ibc-2",query_type="query_channel"} 10
cache_hits{chain="ibc-2",query_type="query_client_state"} 17
cache_hits{chain="ibc-2",query_type="query_connection"} 13
# HELP client_update_message_count Number of MsgUpdateAnyClient relayed
# TYPE client_update_message_count counter
client_update_message_count{chain="ibc-0",counterparty="ibc-1"} 1
client_update_message_count{chain="ibc-1",counterparty="ibc-0"} 1
# HELP ibc_acknowledgment_packets Number of acknowledgment packets relayed per channel
# TYPE ibc_acknowledgment_packets counter
ibc_acknowledgment_packets{src_chain="ibc-0",src_channel="channel-0",src_port="transfer"} 0
ibc_acknowledgment_packets{src_chain="ibc-1",src_channel="channel-0",src_port="transfer"} 0
ibc_acknowledgment_packets{src_chain="ibc-2",src_channel="channel-1",src_port="transfer"} 0
# HELP ibc_receive_packets Number of receive packets relayed per channel
# TYPE ibc_receive_packets counter
ibc_receive_packets{src_chain="ibc-0",src_channel="channel-0",src_port="transfer"} 0
ibc_receive_packets{src_chain="ibc-1",src_channel="channel-0",src_port="transfer"} 0
ibc_receive_packets{src_chain="ibc-2",src_channel="channel-1",src_port="transfer"} 0
# HELP ibc_timeout_packets Number of timeout packets relayed per channel
# TYPE ibc_timeout_packets counter
ibc_timeout_packets{src_chain="ibc-0",src_channel="channel-0",src_port="transfer"} 0
ibc_timeout_packets{src_chain="ibc-1",src_channel="channel-0",src_port="transfer"} 0
ibc_timeout_packets{src_chain="ibc-2",src_channel="channel-1",src_port="transfer"} 0
# HELP msg_num How many messages Hermes submitted to the chain, per chain
# TYPE msg_num counter
msg_num{chain="ibc-0"} 7
msg_num{chain="ibc-1"} 8
msg_num{chain="ibc-2"} 6
# HELP oldest_sequence The sequence number of the oldest pending SendPacket. If this value is 0, it means there are no pending SendPacket.
# TYPE oldest_sequence gauge
oldest_sequence{chain="ibc-0",channel="channel-0",counterparty="ibc-2",port="transfer"} 2037
oldest_sequence{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 3167
oldest_sequence{chain="ibc-2",channel="channel-1",counterparty="ibc-1",port="transfer"} 4954
# HELP oldest_timestamp The timestamp of the oldest sequence number in seconds.
# TYPE oldest_timestamp gauge
oldest_timestamp{chain="ibc-0",channel="channel-0",counterparty="ibc-2",port="transfer"} 1656420717
oldest_timestamp{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 1656420719
oldest_timestamp{chain="ibc-2",channel="channel-1",counterparty="ibc-1",port="transfer"} 1656420717
# HELP queries Number of queries emitted by the relayer, per chain and query type
# TYPE queries counter
queries{chain="ibc-0",query_type="query_application_status"} 33
queries{chain="ibc-0",query_type="query_blocks"} 1
queries{chain="ibc-0",query_type="query_channel"} 14
queries{chain="ibc-0",query_type="query_client_connections"} 9
queries{chain="ibc-0",query_type="query_client_state"} 24
queries{chain="ibc-0",query_type="query_clients"} 1
queries{chain="ibc-0",query_type="query_connection"} 2
queries{chain="ibc-0",query_type="query_connection_channels"} 2
queries{chain="ibc-0",query_type="query_consensus_state"} 29
queries{chain="ibc-0",query_type="query_consensus_states"} 2
queries{chain="ibc-0",query_type="query_latest_height"} 1
queries{chain="ibc-0",query_type="query_packet_acknowledgements"} 3
queries{chain="ibc-0",query_type="query_packet_commitments"} 6
queries{chain="ibc-0",query_type="query_staking_params"} 2
queries{chain="ibc-0",query_type="query_txs"} 188
queries{chain="ibc-0",query_type="query_unreceived_packets"} 13
queries{chain="ibc-1",query_type="query_application_status"} 33
queries{chain="ibc-1",query_type="query_blocks"} 1
queries{chain="ibc-1",query_type="query_channel"} 16
queries{chain="ibc-1",query_type="query_client_connections"} 2
queries{chain="ibc-1",query_type="query_client_state"} 24
queries{chain="ibc-1",query_type="query_clients"} 1
queries{chain="ibc-1",query_type="query_connection"} 2
queries{chain="ibc-1",query_type="query_connection_channels"} 2
queries{chain="ibc-1",query_type="query_consensus_state"} 29
queries{chain="ibc-1",query_type="query_consensus_states"} 2
queries{chain="ibc-1",query_type="query_latest_height"} 1
queries{chain="ibc-1",query_type="query_packet_acknowledgements"} 3
queries{chain="ibc-1",query_type="query_packet_commitments"} 6
queries{chain="ibc-1",query_type="query_staking_params"} 2
queries{chain="ibc-1",query_type="query_txs"} 190
queries{chain="ibc-1",query_type="query_unreceived_packets"} 15
queries{chain="ibc-2",query_type="query_application_status"} 33
queries{chain="ibc-2",query_type="query_blocks"} 1
queries{chain="ibc-2",query_type="query_channel"} 12
queries{chain="ibc-2",query_type="query_client_connections"} 2
queries{chain="ibc-2",query_type="query_client_state"} 24
queries{chain="ibc-2",query_type="query_clients"} 1
queries{chain="ibc-2",query_type="query_connection"} 2
queries{chain="ibc-2",query_type="query_connection_channels"} 2
queries{chain="ibc-2",query_type="query_consensus_state"} 29
queries{chain="ibc-2",query_type="query_consensus_states"} 2
queries{chain="ibc-2",query_type="query_latest_height"} 1
queries{chain="ibc-2",query_type="query_packet_acknowledgements"} 3
queries{chain="ibc-2",query_type="query_packet_commitments"} 6
queries{chain="ibc-2",query_type="query_staking_params"} 2
queries{chain="ibc-2",query_type="query_txs"} 192
queries{chain="ibc-2",query_type="query_unreceived_packets"} 11
# HELP send_packet_count Number of SendPacket relayed.
# TYPE send_packet_count counter
send_packet_count{chain="ibc-0",channel="channel-0",counterparty="ibc-2",port="transfer"} 5
send_packet_count{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 6
send_packet_count{chain="ibc-2",channel="channel-1",counterparty="ibc-1",port="transfer"} 7
# HELP tx_latency_submitted The latency for all transactions submitted to a specific chain, i.e. the difference between the moment when Hermes received a batch of events and when it submitted the corresponding transaction(s). Milliseconds.
# TYPE tx_latency_submitted histogram
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-1",counterparty="ibc-1",port="transfer",le="+Inf"} 1
tx_latency_submitted_sum{chain="ibc-0",channel="channel-1",counterparty="ibc-1",port="transfer"} 298
tx_latency_submitted_count{chain="ibc-0",channel="channel-1",counterparty="ibc-1",port="transfer"} 1
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-1",counterparty="ibc-2",port="transfer",le="+Inf"} 1
tx_latency_submitted_sum{chain="ibc-1",channel="channel-1",counterparty="ibc-2",port="transfer"} 400
tx_latency_submitted_count{chain="ibc-1",channel="channel-1",counterparty="ibc-2",port="transfer"} 1
tx_latency_submitted_bucket{chain="ibc-2",channel="channel-0",counterparty="ibc-0",port="transfer",le="+Inf"} 1
tx_latency_submitted_sum{chain="ibc-2",channel="channel-0",counterparty="ibc-0",port="transfer"} 301
tx_latency_submitted_count{chain="ibc-2",channel="channel-0",counterparty="ibc-0",port="transfer"} 1
# HELP wallet_balance The balance in each wallet that Hermes is using, per wallet, denom and chain. The amount is of unit: 10^6 * `denom`
# TYPE wallet_balance gauge
wallet_balance{account="cosmos1lfq283ph84d49hywahpngxueqsv4wgxt6x5d7z",chain="ibc-0",denom="stake"} 95
wallet_balance{account="cosmos1mmkyea9pmqhlewrap0urpes2vx0r4gnz7eq5vl",chain="ibc-1",denom="stake"} 93
wallet_balance{account="cosmos1pmypcnlkgzfuayzlxr3w9ykp7d0pd4lg027e46",chain="ibc-2",denom="stake"} 94
# HELP workers Number of workers per object
# TYPE workers gauge
workers{type="client"} 6
workers{type="packet"} 3
workers{type="wallet"} 3
# HELP ws_events How many IBC events did Hermes receive via the WebSocket subscription, per chain
# TYPE ws_events counter
ws_events{chain="ibc-0"} 6
ws_events{chain="ibc-1"} 8
ws_events{chain="ibc-2"} 8
```

