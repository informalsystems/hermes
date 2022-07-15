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
| `ibc_receive_packets`        | Number of confirmed receive packets relayed per channel. Available if relayer runs with Tx confirmation enabled        | `u64` Counter       |
| `ibc_acknowledgment_packets` | Number of confirmed acknowledgment packets relayed per channel. Available if relayer runs with Tx confirmation enabled | `u64` Counter       |
| `ibc_timeout_packets`        | Number of confirmed timeout packets relayed per channel. Available if relayer runs with Tx confirmation enabled        | `u64` Counter       |
| `wallet_balance`             | How much balance (coins) there is left in each wallet key that Hermes is using. | `u64` ValueRecorder       |
| `ws_events`                  | How many IBC events did Hermes receive via the websocket subscription, in total since starting up, per chain. | Counter       |
| `ws_reconnect`               | Number of times Hermes had to reconnect to the WebSocket endpoint                                                             | Counter       |
| `tx_latency_submitted`       | Latency for all transactions submitted to a chain (i.e., difference between the moment when Hermes received an event until the corresponding transaction(s) were submitted). | `u64` ValueRecorder       |
| `tx_latency_confirmed`       | Latency for all transactions confirmed by a chain (i.e., difference between the moment when Hermes received an event until the corresponding transaction(s) were confirmed). Requires `tx_confirmation = true`. | `u64` ValueRecorder       |
| `msg_num`                    | How many messages Hermes submitted to a specific chain. | `u64` Counter     |
| `queries`                    | Number of queries emitted by the relayer, per chain and query type | `u64` Counter |
| `query_cache_hits`           | Number of cache hits for queries emitted by the relayer, per chain and query type | `u64` Counter |
| `send_packet_count`          | Number of SendPacket events processed | `u64` Counter |
| `acknowledgement_count`      | Number of WriteAcknowledgement events processed      | `u64` Counter       |
| `cleared_send_packet_count`    | Number of SendPacket events processed during ClearPendingPackets | `u64` Counter   |
| `cleared_acknowledgment_count` | Number of WriteAcknowledgement events processed during ClearPendingPackets | `u64` Counter   |
| `oldest_sequence`            | The sequence number of the oldest SendPacket event observed without its corresponding WriteAcknowledgement event. If this value is 0, it means Hermes observed a WriteAcknowledgment event for all the SendPacket events | `u64` ValueRecorder |
| `oldest_timestamp`           | The timestamp of the oldest sequence number in seconds | `u64` ValueRecorder |

## Integration with Prometheus

With the settings , the telemetry service will be enabled and will serve the metrics using
the Prometheus encoder over HTTP at [`http://localhost:3001/metrics`](http://localhost:3001/metrics).

After starting Hermes with `hermes start`, and letting it run for a while to relay packets,
open [`http://localhost:3001/metrics`](http://localhost:3001/metrics) in a browser, you should
see Prometheus-encoded metrics.

For example, with two channels and after transferring some tokens between the chains:

```text
# HELP acknowledgement_count Number of WriteAcknowledgement events processed
# TYPE acknowledgement_count counter
acknowledgement_count{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 35
# HELP cache_hits Number of cache hits for queries emitted by the relayer, per chain and query type
# TYPE cache_hits counter
cache_hits{chain="ibc-0",query_type="query_channel"} 37
cache_hits{chain="ibc-0",query_type="query_client_state"} 45
cache_hits{chain="ibc-0",query_type="query_connection"} 39
cache_hits{chain="ibc-1",query_type="query_channel"} 57
cache_hits{chain="ibc-1",query_type="query_client_state"} 29
cache_hits{chain="ibc-1",query_type="query_connection"} 24
# HELP cleared_send_packet_count Number of SendPacket events processed during ClearPendingPackets
# TYPE cleared_send_packet_count counter
cleared_send_packet_count{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 15
# HELP ibc_acknowledgment_packets Number of confirmed acknowledgment packets relayed per channel. Available if relayer runs with Tx confirmation enabled
# TYPE ibc_acknowledgment_packets counter
ibc_acknowledgment_packets{src_chain="ibc-0",src_channel="channel-0",src_port="transfer"} 15
ibc_acknowledgment_packets{src_chain="ibc-1",src_channel="channel-0",src_port="transfer"} 0
# HELP ibc_receive_packets Number of confirmed receive packets relayed per channel. Available if relayer runs with Tx confirmation enabled
# TYPE ibc_receive_packets counter
ibc_receive_packets{src_chain="ibc-0",src_channel="channel-0",src_port="transfer"} 0
ibc_receive_packets{src_chain="ibc-1",src_channel="channel-0",src_port="transfer"} 35
# HELP ibc_timeout_packets Number of confirmed timeout packets relayed per channel. Available if relayer runs with Tx confirmation enabled
# TYPE ibc_timeout_packets counter
ibc_timeout_packets{src_chain="ibc-0",src_channel="channel-0",src_port="transfer"} 0
ibc_timeout_packets{src_chain="ibc-1",src_channel="channel-0",src_port="transfer"} 0
# HELP msg_num How many messages Hermes submitted to the chain, per chain
# TYPE msg_num counter
msg_num{chain="ibc-0"} 37
msg_num{chain="ibc-1"} 37
# HELP oldest_sequence The sequence number of the oldest SendPacket event observed without its corresponding WriteAcknowledgement event. If this value is 0, it means Hermes observed a WriteAcknowledgment event for all the SendPacket events
# TYPE oldest_sequence gauge
oldest_sequence{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 0
# HELP oldest_timestamp The timestamp of the oldest sequence number in seconds
# TYPE oldest_timestamp gauge
oldest_timestamp{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 0
# HELP queries Number of queries emitted by the relayer, per chain and query type
# TYPE queries counter
queries{chain="ibc-0",query_type="query_application_status"} 151
queries{chain="ibc-0",query_type="query_channel"} 72
queries{chain="ibc-0",query_type="query_client_connections"} 1
queries{chain="ibc-0",query_type="query_client_state"} 140
queries{chain="ibc-0",query_type="query_clients"} 1
queries{chain="ibc-0",query_type="query_connection"} 1
queries{chain="ibc-0",query_type="query_connection_channels"} 1
queries{chain="ibc-0",query_type="query_consensus_state"} 143
queries{chain="ibc-0",query_type="query_consensus_states"} 1
queries{chain="ibc-0",query_type="query_latest_height"} 1
queries{chain="ibc-0",query_type="query_packet_acknowledgements"} 2
queries{chain="ibc-0",query_type="query_packet_commitments"} 3
queries{chain="ibc-0",query_type="query_staking_params"} 2
queries{chain="ibc-0",query_type="query_txs"} 50
queries{chain="ibc-0",query_type="query_unreceived_packets"} 72
queries{chain="ibc-1",query_type="query_application_status"} 151
queries{chain="ibc-1",query_type="query_channel"} 2
queries{chain="ibc-1",query_type="query_client_connections"} 1
queries{chain="ibc-1",query_type="query_client_state"} 139
queries{chain="ibc-1",query_type="query_clients"} 1
queries{chain="ibc-1",query_type="query_connection"} 1
queries{chain="ibc-1",query_type="query_connection_channels"} 1
queries{chain="ibc-1",query_type="query_consensus_state"} 143
queries{chain="ibc-1",query_type="query_consensus_states"} 1
queries{chain="ibc-1",query_type="query_latest_height"} 1
queries{chain="ibc-1",query_type="query_packet_acknowledgements"} 1
queries{chain="ibc-1",query_type="query_packet_commitments"} 4
queries{chain="ibc-1",query_type="query_staking_params"} 2
queries{chain="ibc-1",query_type="query_txs"} 32
queries{chain="ibc-1",query_type="query_unreceived_acknowledgements"} 71
# HELP send_packet_count Number of SendPacket events processed
# TYPE send_packet_count counter
send_packet_count{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 35
# HELP tx_latency_confirmed The latency for all transactions submitted & confirmed to a specific chain, i.e. the difference between the moment when Hermes received a batch of events until the corresponding transaction(s) were confirmed. Milliseconds.
# TYPE tx_latency_confirmed histogram
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="10"} 0
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="50"} 0
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="100"} 0
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="200"} 0
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="500"} 0
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="1000"} 0
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="2000"} 0
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="+Inf"} 1
tx_latency_confirmed_sum{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 4400
tx_latency_confirmed_count{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 1
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="10"} 0
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="50"} 0
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="100"} 0
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="200"} 0
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="500"} 0
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="1000"} 0
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="2000"} 0
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="+Inf"} 1
tx_latency_confirmed_sum{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 2018
tx_latency_confirmed_count{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 1
# HELP tx_latency_submitted The latency for all transactions submitted to a specific chain, i.e. the difference between the moment when Hermes received a batch of events and when it submitted the corresponding transaction(s). Milliseconds.
# TYPE tx_latency_submitted histogram
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="10"} 0
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="50"} 0
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="100"} 0
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="200"} 0
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="500"} 1
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="1000"} 1
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="2000"} 1
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="+Inf"} 1
tx_latency_submitted_sum{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 361
tx_latency_submitted_count{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 1
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="10"} 0
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="50"} 0
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="100"} 0
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="200"} 0
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="500"} 0
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="1000"} 1
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="2000"} 1
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="+Inf"} 1
tx_latency_submitted_sum{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 573
tx_latency_submitted_count{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 1
# HELP wallet_balance The balance in each wallet that Hermes is using, per wallet, denom and chain. The amount is of unit: 10^6 * `denom`
# TYPE wallet_balance gauge
wallet_balance{account="cosmos12kzv7w2z4ze6f3x67zs0l0r8du9cx7cxm4v7kk",chain="ibc-1",denom="stake"} 99
wallet_balance{account="cosmos1jwgvxl8twq7wv3duy2daevyd5u5v5fw9946p46",chain="ibc-0",denom="stake"} 99
# HELP workers Number of workers per object
# TYPE workers gauge
workers{type="client"} 2
workers{type="packet"} 2
workers{type="wallet"} 2
# HELP ws_events How many IBC events did Hermes receive via the WebSocket subscription, per chain
# TYPE ws_events counter
ws_events{chain="ibc-0"} 63
ws_events{chain="ibc-1"} 62
```

