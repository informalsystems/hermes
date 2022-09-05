# Integration with Prometheus

With the `enabled = true` setting for `telemetry` in your config.toml, the telemetry service will be enabled and will serve the metrics using
the Prometheus encoder over HTTP at [`http://localhost:3001/metrics`](http://localhost:3001/metrics).

After starting Hermes with `hermes start`, and letting it run for a while to relay packets,
open [`http://localhost:3001/metrics`](http://localhost:3001/metrics) in a browser, you should
see Prometheus-encoded metrics.

For example, with two channels and after transferring some tokens between the chains:

```text
# HELP acknowledgement_events Number of WriteAcknowledgement events received
# TYPE acknowledgement_events counter
acknowledgement_events{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 2
acknowledgement_events{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 2
# HELP acknowledgment_packets_confirmed Number of confirmed acknowledgment packets. Available if relayer runs with Tx confirmation enabled
# TYPE acknowledgment_packets_confirmed counter
acknowledgment_packets_confirmed{src_chain="ibc-0",src_channel="channel-0",src_port="transfer"} 2
acknowledgment_packets_confirmed{src_chain="ibc-1",src_channel="channel-0",src_port="transfer"} 2
# HELP backlog_oldest_sequence Sequence number of the oldest SendPacket event in the backlog
# TYPE backlog_oldest_sequence gauge
backlog_oldest_sequence{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 0
backlog_oldest_sequence{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 0
# HELP backlog_oldest_timestamp Local timestamp for the oldest SendPacket event in the backlog
# TYPE backlog_oldest_timestamp gauge
backlog_oldest_timestamp{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 0
backlog_oldest_timestamp{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 0
# HELP backlog_size Total number of SendPacket events in the backlog
# TYPE backlog_size gauge
backlog_size{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 0
backlog_size{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 0
# HELP client_updates_submitted Number of client update messages submitted
# TYPE client_updates_submitted counter
client_updates_submitted{chain="ibc-0",client="07-tendermint-0"} 8
client_updates_submitted{chain="ibc-1",client="07-tendermint-0"} 19
# HELP queries Number of queries submitted by Hermes
# TYPE queries counter
queries{chain="ibc-0",query_type="query_application_status"} 486
queries{chain="ibc-0",query_type="query_channel"} 20
queries{chain="ibc-0",query_type="query_client_state"} 375
queries{chain="ibc-0",query_type="query_clients"} 1
queries{chain="ibc-0",query_type="query_commitment_prefix"} 2
queries{chain="ibc-0",query_type="query_connection"} 21
queries{chain="ibc-0",query_type="query_consensus_state"} 373
queries{chain="ibc-0",query_type="query_consensus_states"} 2
queries{chain="ibc-0",query_type="query_latest_height"} 1
queries{chain="ibc-0",query_type="query_packet_acknowledgements"} 2
queries{chain="ibc-0",query_type="query_packet_commitments"} 3
queries{chain="ibc-0",query_type="query_staking_params"} 2
queries{chain="ibc-0",query_type="query_txs"} 48
queries{chain="ibc-0",query_type="query_unreceived_acknowledgements"} 4
queries{chain="ibc-0",query_type="query_unreceived_packets"} 5
queries{chain="ibc-1",query_type="query_application_status"} 449
queries{chain="ibc-1",query_type="query_blocks"} 1
queries{chain="ibc-1",query_type="query_channel"} 21
queries{chain="ibc-1",query_type="query_client_connections"} 3
queries{chain="ibc-1",query_type="query_client_state"} 367
queries{chain="ibc-1",query_type="query_clients"} 1
queries{chain="ibc-1",query_type="query_commitment_prefix"} 2
queries{chain="ibc-1",query_type="query_connection"} 22
queries{chain="ibc-1",query_type="query_connection_channels"} 5
queries{chain="ibc-1",query_type="query_connections"} 6
queries{chain="ibc-1",query_type="query_consensus_state"} 372
queries{chain="ibc-1",query_type="query_consensus_states"} 2
queries{chain="ibc-1",query_type="query_latest_height"} 1
queries{chain="ibc-1",query_type="query_packet_acknowledgements"} 1
queries{chain="ibc-1",query_type="query_packet_commitments"} 3
queries{chain="ibc-1",query_type="query_staking_params"} 2
queries{chain="ibc-1",query_type="query_txs"} 40
queries{chain="ibc-1",query_type="query_unreceived_acknowledgements"} 5
queries{chain="ibc-1",query_type="query_unreceived_packets"} 4
# HELP queries_cache_hits Number of cache hits for queries submitted by Hermes
# TYPE queries_cache_hits counter
queries_cache_hits{chain="ibc-0",query_type="query_channel"} 13
queries_cache_hits{chain="ibc-0",query_type="query_client_state"} 29
queries_cache_hits{chain="ibc-0",query_type="query_connection"} 29
queries_cache_hits{chain="ibc-0",query_type="query_latest_height"} 133
queries_cache_hits{chain="ibc-1",query_type="query_channel"} 6
queries_cache_hits{chain="ibc-1",query_type="query_client_state"} 50
queries_cache_hits{chain="ibc-1",query_type="query_connection"} 17
queries_cache_hits{chain="ibc-1",query_type="query_latest_height"} 64
# HELP receive_packets_confirmed Number of confirmed receive packets. Available if relayer runs with Tx confirmation enabled
# TYPE receive_packets_confirmed counter
receive_packets_confirmed{src_chain="ibc-0",src_channel="channel-0",src_port="transfer"} 2
receive_packets_confirmed{src_chain="ibc-1",src_channel="channel-0",src_port="transfer"} 2
# HELP send_packet_events Number of SendPacket events received
# TYPE send_packet_events counter
send_packet_events{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 2
send_packet_events{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 2
# HELP total_messages_submitted Number of messages submitted to a specific chain
# TYPE total_messages_submitted counter
total_messages_submitted{chain="ibc-0"} 11
total_messages_submitted{chain="ibc-1"} 22
# HELP tx_latency_confirmed The latency for all transactions submitted & confirmed to a specific chain, i.e. the difference between the moment when Hermes received a batch of events until the corresponding transaction(s) were confirmed. Milliseconds.
# TYPE tx_latency_confirmed histogram
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="1000"} 0
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="5000"} 4
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="9000"} 4
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="13000"} 4
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="17000"} 4
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="20000"} 4
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="+Inf"} 4
tx_latency_confirmed_sum{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 14265
tx_latency_confirmed_count{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 4
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="1000"} 0
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="5000"} 4
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="9000"} 4
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="13000"} 4
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="17000"} 4
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="20000"} 4
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="+Inf"} 4
tx_latency_confirmed_sum{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 10103
tx_latency_confirmed_count{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 4
# HELP tx_latency_submitted The latency for all transactions submitted to a specific chain, i.e. the difference between the moment when Hermes received a batch of events and when it submitted the corresponding transaction(s). Milliseconds.
# TYPE tx_latency_submitted histogram
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="200"} 0
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="500"} 2
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="1000"} 4
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="2000"} 4
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="5000"} 4
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="10000"} 4
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",le="+Inf"} 4
tx_latency_submitted_sum{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 1941
tx_latency_submitted_count{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer"} 4
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="200"} 0
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="500"} 0
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="1000"} 4
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="2000"} 4
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="5000"} 4
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="10000"} 4
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",le="+Inf"} 4
tx_latency_submitted_sum{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 2535
tx_latency_submitted_count{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer"} 4
# HELP wallet_balance The balance of each wallet Hermes uses per chain. Please note that when converting the balance to f64 a loss in precision might be introduced in the displayed value
# TYPE wallet_balance gauge
wallet_balance{account="cosmos1a450s556xf9n63vdd9aet6g6t29tm207ygp5rj",chain="ibc-1",denom="stake"} 99969960
wallet_balance{account="cosmos1fafdyl4hl0ltcx4c3y9zhnkf5uxcah9tefuavy",chain="ibc-0",denom="stake"} 99983143
# HELP workers Number of workers
# TYPE workers gauge
workers{type="channel"} 3
workers{type="client"} 2
workers{type="connection"} 3
workers{type="packet"} 2
workers{type="wallet"} 2
# HELP ws_events How many IBC events did Hermes receive via the websocket subscription
# TYPE ws_events counter
ws_events{chain="ibc-0"} 115
ws_events{chain="ibc-1"} 128
```
