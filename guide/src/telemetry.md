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

| Name                         | Description                                          | OpenTelemetry type  | Configuration dependencies |
| ---------------------------- | ---------------------------------------------------- | ------------------- | -------------------------- |
| `workers`                    | Number of workers per object                         | `i64` UpDownCounter | Corresponding workers enabled |
| `ibc_client_updates`         | Number of client updates performed per client        | `u64` Counter       | Client workers enabled |
| `ibc_client_misbehaviours`   | Number of misbehaviours detected per client          | `u64` Counter       | Client workers enabled and Clients misbehaviour detection enabled |
| `ibc_receive_packets`        | Number of confirmed receive packets relayed per channel        | `u64` Counter       | Packet workers enabled and Transaction confirmation enabled |
| `ibc_acknowledgment_packets` | Number of confirmed acknowledgment packets relayed per channel | `u64` Counter       | Packet workers enabled and Transaction confirmation enabled |
| `ibc_timeout_packets`        | Number of confirmed timeout packets relayed per channel        | `u64` Counter       | Packet workers enabled and Transaction confirmation enabled |
| `wallet_balance`             | The balance of each wallet Hermes uses per chain. Please note that when converting the balance to f64 a loss in precision might be introduced in the displayed value     | `f64` ValueRecorder | None                       |
| `ws_events`                  | How many IBC events did Hermes receive via the websocket subscription, in total since starting up, per chain. | Counter       | None                       |
| `ws_reconnect`               | Number of times Hermes had to reconnect to the WebSocket endpoint                                                             | Counter       | None                       |
| `tx_latency_submitted`       | Latency for all transactions submitted to a chain (i.e., difference between the moment when Hermes received an event until the corresponding transaction(s) were submitted). | `u64` ValueRecorder       | None                       |
| `tx_latency_confirmed`       | Latency for all transactions confirmed by a chain (i.e., difference between the moment when Hermes received an event until the corresponding transaction(s) were confirmed). Requires `tx_confirmation = true`. | `u64` ValueRecorder       | Transaction confirmation enabled |
| `msg_num`                    | How many messages Hermes submitted to a specific chain. | `u64` Counter     | None                       |
| `queries`                    | Number of queries emitted by the relayer, per chain and query type | `u64` Counter | None                       |
| `query_cache_hits`           | Number of cache hits for queries emitted by the relayer, per chain and query type | `u64` Counter | None                       |
| `send_packet_count`          | Number of SendPacket events processed | `u64` Counter                      | Packet workers enabled     |
| `acknowledgement_count`      | Number of WriteAcknowledgement events processed      | `u64` Counter       | Packet workers enabled     |
| `cleared_send_packet_count`    | Number of SendPacket events processed during the initial and periodic clearing | `u64` Counter   | Packet workers enabled, and periodic packet clearing or clear on start enabled |
| `cleared_acknowledgment_count` | Number of WriteAcknowledgement events processed during the initial and periodic clearing | `u64` Counter   | Packet workers enabled, and periodic packet clearing or clear on start enabled |
| `backlog_oldest_sequence`      | Sequence number of the oldest pending packet in the backlog, per channel | `u64` ValueRecorder | Packet workers enabled     |
| `backlog_oldest_timestamp`     | Local timestamp for the oldest pending packet in the backlog, per channel | `u64` ValueRecorder | Packet workers enabled     |
| `backlog_size`                 | Total number of pending packets, per channel | `u64` ValueRecorder | Packet workers enabled     |

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
acknowledgement_count{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 25
# HELP cache_hits Number of cache hits for queries emitted by the relayer, per chain and query type
# TYPE cache_hits counter
cache_hits{chain="ibc-0",query_type="query_channel"} 63
cache_hits{chain="ibc-0",query_type="query_client_state"} 25
cache_hits{chain="ibc-0",query_type="query_connection"} 19
cache_hits{chain="ibc-1",query_type="query_channel"} 28
cache_hits{chain="ibc-1",query_type="query_client_state"} 36
cache_hits{chain="ibc-1",query_type="query_connection"} 29
# HELP cleared_acknowledgment_count Number of WriteAcknowledgment events processed during the initial and periodic clearing
# TYPE cleared_acknowledgment_count counter
cleared_acknowledgment_count{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 20
# HELP cleared_send_packet_count Number of SendPacket events processed during the initial and periodic clearing
# TYPE cleared_send_packet_count counter
cleared_send_packet_count{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 10
# HELP ibc_acknowledgment_packets Number of confirmed acknowledgment packets relayed per channel. Available if relayer runs with Tx confirmation enabled
# TYPE ibc_acknowledgment_packets counter
ibc_acknowledgment_packets{src_chain="ibc-1",src_channel="channel-0",src_port="transfer"} 30
# HELP ibc_receive_packets Number of confirmed receive packets relayed per channel. Available if relayer runs with Tx confirmation enabled
# TYPE ibc_receive_packets counter
ibc_receive_packets{src_chain="ibc-0",src_channel="channel-0",src_port="transfer"} 25
# HELP msg_num How many messages Hermes submitted to the chain, per chain
# TYPE msg_num counter
msg_num{chain="ibc-0"} 48
msg_num{chain="ibc-1"} 27
# HELP oldest_sequence The sequence number of the oldest SendPacket event observed without its corresponding WriteAcknowledgement event. If this value is 0, it means Hermes observed a WriteAcknowledgment event for all the SendPacket events
# TYPE oldest_sequence gauge
oldest_sequence{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 0
# HELP oldest_timestamp The timestamp of the oldest sequence number in seconds
# TYPE oldest_timestamp gauge
oldest_timestamp{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 0
# HELP queries Number of queries emitted by the relayer, per chain and query type
# TYPE queries counter
queries{chain="ibc-0",query_type="query_application_status"} 71
queries{chain="ibc-0",query_type="query_channel"} 1
queries{chain="ibc-0",query_type="query_client_connections"} 1
queries{chain="ibc-0",query_type="query_client_state"} 58
queries{chain="ibc-0",query_type="query_clients"} 1
queries{chain="ibc-0",query_type="query_connection"} 1
queries{chain="ibc-0",query_type="query_connection_channels"} 1
queries{chain="ibc-0",query_type="query_consensus_state"} 61
queries{chain="ibc-0",query_type="query_consensus_states"} 1
queries{chain="ibc-0",query_type="query_latest_height"} 1
queries{chain="ibc-0",query_type="query_packet_acknowledgements"} 1
queries{chain="ibc-0",query_type="query_packet_commitments"} 4
queries{chain="ibc-0",query_type="query_staking_params"} 2
queries{chain="ibc-0",query_type="query_txs"} 32
queries{chain="ibc-0",query_type="query_unreceived_acknowledgements"} 92
queries{chain="ibc-1",query_type="query_application_status"} 70
queries{chain="ibc-1",query_type="query_channel"} 51
queries{chain="ibc-1",query_type="query_client_connections"} 1
queries{chain="ibc-1",query_type="query_client_state"} 56
queries{chain="ibc-1",query_type="query_clients"} 1
queries{chain="ibc-1",query_type="query_connection"} 1
queries{chain="ibc-1",query_type="query_connection_channels"} 1
queries{chain="ibc-1",query_type="query_consensus_state"} 60
queries{chain="ibc-1",query_type="query_consensus_states"} 1
queries{chain="ibc-1",query_type="query_latest_height"} 1
queries{chain="ibc-1",query_type="query_packet_acknowledgements"} 2
queries{chain="ibc-1",query_type="query_packet_commitments"} 3
queries{chain="ibc-1",query_type="query_staking_params"} 2
queries{chain="ibc-1",query_type="query_txs"} 38
queries{chain="ibc-1",query_type="query_unreceived_packets"} 52
# HELP send_packet_count Number of SendPacket events processed
# TYPE send_packet_count counter
send_packet_count{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 25
# HELP tx_latency_confirmed The latency for all transactions submitted & confirmed to a specific chain, i.e. the difference between the moment when Hermes received a batch of events until the corresponding transaction(s) were confirmed. Milliseconds.
# TYPE tx_latency_confirmed histogram
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="1000"} 0
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="5000"} 2
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="9000"} 2
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="13000"} 2
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="17000"} 2
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="20000"} 2
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="+Inf"} 2
tx_latency_confirmed_sum{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 7518
tx_latency_confirmed_count{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 2
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="1000"} 0
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="5000"} 2
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="9000"} 2
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="13000"} 2
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="17000"} 2
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="20000"} 2
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="+Inf"} 2
tx_latency_confirmed_sum{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 5291
tx_latency_confirmed_count{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 2
# HELP tx_latency_submitted The latency for all transactions submitted to a specific chain, i.e. the difference between the moment when Hermes received a batch of events and when it submitted the corresponding transaction(s). Milliseconds.
# TYPE tx_latency_submitted histogram
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="200"} 0
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="500"} 1
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="1000"} 2
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="2000"} 2
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="5000"} 2
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="10000"} 2
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="+Inf"} 2
tx_latency_submitted_sum{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 1175
tx_latency_submitted_count{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 2
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="200"} 1
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="500"} 2
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="1000"} 2
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="2000"} 2
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="5000"} 2
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="10000"} 2
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="+Inf"} 2
tx_latency_submitted_sum{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 542
tx_latency_submitted_count{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 2
# HELP wallet_balance The balance of each wallet Hermes uses per chain. Please note that when converting the balance to f64 a loss in precision might be introduced in the displayed value
# TYPE wallet_balance gauge
wallet_balance{account="cosmos1a9emd54sp0xsw77e2pzcc2pjfp7jvtl64p64w7",chain="ibc-1",denom="stake"} 99940782
wallet_balance{account="cosmos1s9jwwt60edxhy0ez84h3wfujerj5mgzhmasy23",chain="ibc-0",denom="stake"} 99962295
# HELP workers Number of workers per object
# TYPE workers gauge
workers{type="client"} 2
workers{type="packet"} 2
workers{type="wallet"} 2
# HELP ws_events How many IBC events did Hermes receive via the WebSocket subscription, per chain
# TYPE ws_events counter
ws_events{chain="ibc-0"} 57
ws_events{chain="ibc-1"} 37
```
