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
| `msg_num`                    | How many messages Hermes submitted to a specific chain. | `u64` Counter       |

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
cache_hits{chain="ibc-0",query_type="query_channel"} 276
cache_hits{chain="ibc-0",query_type="query_client_state"} 177
cache_hits{chain="ibc-0",query_type="query_connection"} 160
cache_hits{chain="ibc-1",query_type="query_channel"} 240
cache_hits{chain="ibc-1",query_type="query_client_state"} 173
cache_hits{chain="ibc-1",query_type="query_connection"} 160
# HELP ibc_acknowledgment_packets Number of acknowledgment packets relayed per channel
# TYPE ibc_acknowledgment_packets counter
ibc_acknowledgment_packets{src_chain="ibc-0",src_channel="channel-0",src_port="transfer"} 0
ibc_acknowledgment_packets{src_chain="ibc-0",src_channel="channel-1",src_port="transfer"} 42
ibc_acknowledgment_packets{src_chain="ibc-1",src_channel="channel-0",src_port="transfer"} 110
ibc_acknowledgment_packets{src_chain="ibc-1",src_channel="channel-1",src_port="transfer"} 0
# HELP ibc_receive_packets Number of receive packets relayed per channel
# TYPE ibc_receive_packets counter
ibc_receive_packets{src_chain="ibc-0",src_channel="channel-0",src_port="transfer"} 110
ibc_receive_packets{src_chain="ibc-0",src_channel="channel-1",src_port="transfer"} 0
ibc_receive_packets{src_chain="ibc-1",src_channel="channel-0",src_port="transfer"} 0
ibc_receive_packets{src_chain="ibc-1",src_channel="channel-1",src_port="transfer"} 42
# HELP ibc_timeout_packets Number of timeout packets relayed per channel
# TYPE ibc_timeout_packets counter
ibc_timeout_packets{src_chain="ibc-0",src_channel="channel-0",src_port="transfer"} 0
ibc_timeout_packets{src_chain="ibc-0",src_channel="channel-1",src_port="transfer"} 0
ibc_timeout_packets{src_chain="ibc-1",src_channel="channel-0",src_port="transfer"} 0
ibc_timeout_packets{src_chain="ibc-1",src_channel="channel-1",src_port="transfer"} 0
# HELP msg_num How many messages Hermes submitted to the chain, per chain
# TYPE msg_num counter
msg_num{chain="ibc-0"} 168
msg_num{chain="ibc-1"} 156
# HELP queries Number of queries emitted by the relayer, per chain and query type
# TYPE queries counter
queries{chain="ibc-0",query_type="query_application_status"} 23
queries{chain="ibc-0",query_type="query_channel"} 88
queries{chain="ibc-0",query_type="query_client_connections"} 2
queries{chain="ibc-0",query_type="query_client_state"} 383
queries{chain="ibc-0",query_type="query_clients"} 1
queries{chain="ibc-0",query_type="query_connection"} 2
queries{chain="ibc-0",query_type="query_connection_channels"} 2
queries{chain="ibc-0",query_type="query_consensus_state"} 392
queries{chain="ibc-0",query_type="query_consensus_states"} 2
queries{chain="ibc-0",query_type="query_latest_height"} 1
queries{chain="ibc-0",query_type="query_packet_acknowledgements"} 5
queries{chain="ibc-0",query_type="query_packet_commitments"} 10
queries{chain="ibc-0",query_type="query_staking_params"} 2
queries{chain="ibc-0",query_type="query_txs"} 76
queries{chain="ibc-0",query_type="query_unreceived_acknowledgements"} 241
queries{chain="ibc-0",query_type="query_unreceived_packets"} 127
queries{chain="ibc-1",query_type="query_application_status"} 20
queries{chain="ibc-1",query_type="query_channel"} 224
queries{chain="ibc-1",query_type="query_client_connections"} 2
queries{chain="ibc-1",query_type="query_client_state"} 387
queries{chain="ibc-1",query_type="query_clients"} 1
queries{chain="ibc-1",query_type="query_connection"} 2
queries{chain="ibc-1",query_type="query_connection_channels"} 2
queries{chain="ibc-1",query_type="query_consensus_state"} 394
queries{chain="ibc-1",query_type="query_consensus_states"} 3
queries{chain="ibc-1",query_type="query_latest_height"} 1
queries{chain="ibc-1",query_type="query_packet_acknowledgements"} 5
queries{chain="ibc-1",query_type="query_packet_commitments"} 10
queries{chain="ibc-1",query_type="query_staking_params"} 2
queries{chain="ibc-1",query_type="query_txs"} 56
queries{chain="ibc-1",query_type="query_unreceived_acknowledgements"} 127
queries{chain="ibc-1",query_type="query_unreceived_packets"} 292
# HELP tx_latency_confirmed The latency for all transactions submitted to a specific chain, i.e. the difference between the moment when Hermes received a batch of events until the corresponding transaction(s) were confirmed. Milliseconds.
# TYPE tx_latency_confirmed histogram
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="0.5"} 0
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="0.9"} 0
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="0.99"} 0
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="+Inf"} 4
tx_latency_confirmed_sum{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 22466
tx_latency_confirmed_count{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 4
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-1",counterparty="ibc-1",port="transfer",le="0.5"} 0
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-1",counterparty="ibc-1",port="transfer",le="0.9"} 0
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-1",counterparty="ibc-1",port="transfer",le="0.99"} 0
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-1",counterparty="ibc-1",port="transfer",le="+Inf"} 1
tx_latency_confirmed_sum{chain="ibc-0",channel="channel-1",counterparty="ibc-1",port="transfer"} 4256
tx_latency_confirmed_count{chain="ibc-0",channel="channel-1",counterparty="ibc-1",port="transfer"} 1
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="0.5"} 0
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="0.9"} 0
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="0.99"} 0
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="+Inf"} 2
tx_latency_confirmed_sum{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 9408
tx_latency_confirmed_count{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 2
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-1",counterparty="ibc-0",port="transfer",le="0.5"} 0
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-1",counterparty="ibc-0",port="transfer",le="0.9"} 0
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-1",counterparty="ibc-0",port="transfer",le="0.99"} 0
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-1",counterparty="ibc-0",port="transfer",le="+Inf"} 1
tx_latency_confirmed_sum{chain="ibc-1",channel="channel-1",counterparty="ibc-0",port="transfer"} 3173
tx_latency_confirmed_count{chain="ibc-1",channel="channel-1",counterparty="ibc-0",port="transfer"} 1
# HELP tx_latency_submitted The latency for all transactions submitted to a specific chain, i.e. the difference between the moment when Hermes received a batch of events and when it submitted the corresponding transaction(s). Milliseconds.
# TYPE tx_latency_submitted histogram
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="0.5"} 0
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="0.9"} 0
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="0.99"} 0
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="+Inf"} 5
tx_latency_submitted_sum{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 14428
tx_latency_submitted_count{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 5
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-1",counterparty="ibc-1",port="transfer",le="0.5"} 0
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-1",counterparty="ibc-1",port="transfer",le="0.9"} 0
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-1",counterparty="ibc-1",port="transfer",le="0.99"} 0
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-1",counterparty="ibc-1",port="transfer",le="+Inf"} 1
tx_latency_submitted_sum{chain="ibc-0",channel="channel-1",counterparty="ibc-1",port="transfer"} 729
tx_latency_submitted_count{chain="ibc-0",channel="channel-1",counterparty="ibc-1",port="transfer"} 1
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="0.5"} 0
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="0.9"} 0
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="0.99"} 0
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="+Inf"} 2
tx_latency_submitted_sum{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 1706
tx_latency_submitted_count{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 2
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-1",counterparty="ibc-0",port="transfer",le="0.5"} 0
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-1",counterparty="ibc-0",port="transfer",le="0.9"} 0
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-1",counterparty="ibc-0",port="transfer",le="0.99"} 0
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-1",counterparty="ibc-0",port="transfer",le="+Inf"} 1
tx_latency_submitted_sum{chain="ibc-1",channel="channel-1",counterparty="ibc-0",port="transfer"} 791
tx_latency_submitted_count{chain="ibc-1",channel="channel-1",counterparty="ibc-0",port="transfer"} 1
# HELP wallet_balance The balance in each wallet that Hermes is using, per wallet, denom and chain
# TYPE wallet_balance gauge
wallet_balance{account="cosmos1934akx97773lsjjs9x74dr03uuam29hcc9grp3",chain="ibc-0",denom="stake"} 99999970473
wallet_balance{account="cosmos1hngzqscyg476nd68qggxps8r2aq56lne45ps8n",chain="ibc-1",denom="stake"} 99999978431
# HELP workers Number of workers per object
# TYPE workers gauge
workers{type="client"} 4
workers{type="packet"} 4
workers{type="wallet"} 2
# HELP ws_events How many IBC events did Hermes receive via the WebSocket subscription, per chain
# TYPE ws_events counter
ws_events{chain="ibc-0"} 443
ws_events{chain="ibc-1"} 370
```

