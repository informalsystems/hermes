# Integration with Prometheus

With the `enabled = true` setting for `telemetry` in your config.toml, the telemetry service will be enabled and will serve the metrics using
the Prometheus encoder over HTTP at [`http://localhost:3001/metrics`](http://localhost:3001/metrics).

After starting Hermes with `{{#template ../../templates/commands/hermes/start_1.md}}`, and letting it run for a while to relay packets,
open [`http://localhost:3001/metrics`](http://localhost:3001/metrics) in a browser, you should
see Prometheus-encoded metrics.

For example, with two channels and after transferring some tokens between the chains:

```text
# HELP acknowledgement_events_total Number of WriteAcknowledgement events received
# TYPE acknowledgement_events_total counter
acknowledgement_events_total{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 4
acknowledgement_events_total{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
# HELP acknowledgment_packets_confirmed_total Number of confirmed acknowledgment packets. Available if relayer runs with Tx confirmation enabled
# TYPE acknowledgment_packets_confirmed_total counter
acknowledgment_packets_confirmed_total{dst_chain="ibc-0",dst_channel="channel-0",dst_port="transfer",service_name="unknown_service",src_chain="ibc-1",src_channel="channel-0",src_port="transfer",otel_scope_name="hermes",otel_scope_version=""} 1
acknowledgment_packets_confirmed_total{dst_chain="ibc-1",dst_channel="channel-0",dst_port="transfer",service_name="unknown_service",src_chain="ibc-0",src_channel="channel-0",src_port="transfer",otel_scope_name="hermes",otel_scope_version=""} 0
# HELP backlog_oldest_sequence Sequence number of the oldest SendPacket event in the backlog
# TYPE backlog_oldest_sequence gauge
backlog_oldest_sequence{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
backlog_oldest_sequence{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
# HELP backlog_latest_update_timestamp Local timestamp for the last time the backlog metrics have been updated
# TYPE backlog_latest_update_timestamp gauge
backlog_latest_update_timestamp{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
backlog_latest_update_timestamp{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
# HELP backlog_size Total number of SendPacket events in the backlog
# TYPE backlog_size gauge
backlog_size{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
backlog_size{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
# HELP client_updates_submitted_total Number of client update messages submitted
# TYPE client_updates_submitted_total counter
client_updates_submitted_total{client="07-tendermint-0",dst_chain="ibc-0",service_name="unknown_service",src_chain="ibc-1",otel_scope_name="hermes",otel_scope_version=""} 2
client_updates_submitted_total{client="07-tendermint-0",dst_chain="ibc-1",service_name="unknown_service",src_chain="ibc-0",otel_scope_name="hermes",otel_scope_version=""} 2
# HELP client_updates_skipped_total Number of client update messages skipped
# TYPE client_updates_skipped_total counter
client_updates_skipped_total{client="07-tendermint-0",dst_chain="ibc-0",service_name="unknown_service",src_chain="ibc-1",otel_scope_name="hermes",otel_scope_version=""} 0
client_updates_skipped_total{client="07-tendermint-0",dst_chain="ibc-1",service_name="unknown_service",src_chain="ibc-0",otel_scope_name="hermes",otel_scope_version=""} 0
# HELP ics29_period_fees Amount of ICS29 fees rewarded over the past 7 days
# TYPE ics29_period_fees gauge
ics29_period_fees{chain="ibc-0",denom="stake",receiver="cosmos1j6z6q9d2gf2suav88z8g3zf726vz9ehg4hkr8x",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
ics29_period_fees{chain="ibc-1",denom="stake",receiver="cosmos1340jyu3hawjzusu4jfwh29prpglkju5rlkpesn",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
ics29_period_fees{chain="ibc-2",denom="stake",receiver="cosmos1yxzuet72f4qlks8tzrna6y2q4wchur02gqs5al",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
ics29_period_fees{chain="ibc-3",denom="stake",receiver="cosmos1fk5ykcvkgr4yzlzfyegnaaqyc0ulv8wv8u9hjl",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
# HELP messages_submitted_total Number of messages submitted to a specific chain
# TYPE messages_submitted_total counter
messages_submitted_total{chain="ibc-0",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 7
messages_submitted_total{chain="ibc-1",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 7
messages_submitted_total{chain="ibc-2",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
messages_submitted_total{chain="ibc-3",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
# HELP otel_scope_info Instrumentation Scope metadata
# TYPE otel_scope_info gauge
otel_scope_info{otel_scope_name="hermes",otel_scope_version=""} 1
# HELP queries_cache_hits_total Number of cache hits for queries submitted by Hermes
# TYPE queries_cache_hits_total counter
queries_cache_hits_total{chain="ibc-0",query_type="query_channel",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 9
queries_cache_hits_total{chain="ibc-0",query_type="query_client_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 4
queries_cache_hits_total{chain="ibc-0",query_type="query_connection",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 11
queries_cache_hits_total{chain="ibc-0",query_type="query_latest_height",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_cache_hits_total{chain="ibc-1",query_type="query_channel",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 12
queries_cache_hits_total{chain="ibc-1",query_type="query_client_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 4
queries_cache_hits_total{chain="ibc-1",query_type="query_connection",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 11
queries_cache_hits_total{chain="ibc-1",query_type="query_latest_height",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_cache_hits_total{chain="ibc-2",query_type="query_channel",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_cache_hits_total{chain="ibc-2",query_type="query_client_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_cache_hits_total{chain="ibc-2",query_type="query_connection",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_cache_hits_total{chain="ibc-2",query_type="query_latest_height",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_cache_hits_total{chain="ibc-3",query_type="query_channel",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_cache_hits_total{chain="ibc-3",query_type="query_client_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_cache_hits_total{chain="ibc-3",query_type="query_connection",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_cache_hits_total{chain="ibc-3",query_type="query_latest_height",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
# HELP queries_total Number of queries submitted by Hermes
# TYPE queries_total counter
queries_total{chain="ibc-0",query_type="query_application_status",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 10
queries_total{chain="ibc-0",query_type="query_block",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-0",query_type="query_blocks",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-0",query_type="query_channel",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 9
queries_total{chain="ibc-0",query_type="query_channel_client_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-0",query_type="query_channels",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-0",query_type="query_client_connections",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 2
queries_total{chain="ibc-0",query_type="query_client_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 6
queries_total{chain="ibc-0",query_type="query_clients",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
queries_total{chain="ibc-0",query_type="query_commitment_prefix",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-0",query_type="query_config_params",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
queries_total{chain="ibc-0",query_type="query_connection",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 2
queries_total{chain="ibc-0",query_type="query_connection_channels",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 2
queries_total{chain="ibc-0",query_type="query_connections",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-0",query_type="query_consensus_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 2
queries_total{chain="ibc-0",query_type="query_consensus_states",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-0",query_type="query_latest_height",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
queries_total{chain="ibc-0",query_type="query_next_sequence_receive",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-0",query_type="query_packet_acknowledgements",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
queries_total{chain="ibc-0",query_type="query_packet_commitments",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 2
queries_total{chain="ibc-0",query_type="query_packet_events",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-0",query_type="query_staking_params",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 2
queries_total{chain="ibc-0",query_type="query_txs",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 28
queries_total{chain="ibc-0",query_type="query_unreceived_acknowledgements",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 2
queries_total{chain="ibc-0",query_type="query_unreceived_packets",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 8
queries_total{chain="ibc-0",query_type="query_upgraded_consensus_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-0",query_type="status",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
queries_total{chain="ibc-1",query_type="query_application_status",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 10
queries_total{chain="ibc-1",query_type="query_block",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-1",query_type="query_blocks",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-1",query_type="query_channel",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 3
queries_total{chain="ibc-1",query_type="query_channel_client_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-1",query_type="query_channels",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-1",query_type="query_client_connections",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 2
queries_total{chain="ibc-1",query_type="query_client_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 6
queries_total{chain="ibc-1",query_type="query_clients",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
queries_total{chain="ibc-1",query_type="query_commitment_prefix",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-1",query_type="query_config_params",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
queries_total{chain="ibc-1",query_type="query_connection",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 2
queries_total{chain="ibc-1",query_type="query_connection_channels",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 2
queries_total{chain="ibc-1",query_type="query_connections",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-1",query_type="query_consensus_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 2
queries_total{chain="ibc-1",query_type="query_consensus_states",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-1",query_type="query_latest_height",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
queries_total{chain="ibc-1",query_type="query_next_sequence_receive",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-1",query_type="query_packet_acknowledgements",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
queries_total{chain="ibc-1",query_type="query_packet_commitments",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 2
queries_total{chain="ibc-1",query_type="query_packet_events",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-1",query_type="query_staking_params",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 2
queries_total{chain="ibc-1",query_type="query_txs",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 20
queries_total{chain="ibc-1",query_type="query_unreceived_acknowledgements",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 8
queries_total{chain="ibc-1",query_type="query_unreceived_packets",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 2
queries_total{chain="ibc-1",query_type="query_upgraded_consensus_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-1",query_type="status",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
queries_total{chain="ibc-2",query_type="query_application_status",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_block",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_blocks",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_channel",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_channel_client_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_channels",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_client_connections",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_client_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_clients",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
queries_total{chain="ibc-2",query_type="query_commitment_prefix",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_config_params",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
queries_total{chain="ibc-2",query_type="query_connection",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_connection_channels",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_connections",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_consensus_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_consensus_states",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_latest_height",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
queries_total{chain="ibc-2",query_type="query_next_sequence_receive",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_packet_acknowledgements",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_packet_commitments",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_packet_events",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_staking_params",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 2
queries_total{chain="ibc-2",query_type="query_txs",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_unreceived_acknowledgements",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_unreceived_packets",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="query_upgraded_consensus_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-2",query_type="status",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
queries_total{chain="ibc-3",query_type="query_application_status",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_block",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_blocks",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_channel",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_channel_client_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_channels",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_client_connections",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_client_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_clients",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
queries_total{chain="ibc-3",query_type="query_commitment_prefix",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_config_params",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
queries_total{chain="ibc-3",query_type="query_connection",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_connection_channels",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_connections",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_consensus_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_consensus_states",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_latest_height",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
queries_total{chain="ibc-3",query_type="query_next_sequence_receive",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_packet_acknowledgements",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_packet_commitments",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_packet_events",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_staking_params",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 2
queries_total{chain="ibc-3",query_type="query_txs",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_unreceived_acknowledgements",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_unreceived_packets",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="query_upgraded_consensus_state",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
queries_total{chain="ibc-3",query_type="status",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
# HELP receive_packets_confirmed_total Number of confirmed receive packets. Available if relayer runs with Tx confirmation enabled
# TYPE receive_packets_confirmed_total counter
receive_packets_confirmed_total{dst_chain="ibc-0",dst_channel="channel-0",dst_port="transfer",service_name="unknown_service",src_chain="ibc-1",src_channel="channel-0",src_port="transfer",otel_scope_name="hermes",otel_scope_version=""} 4
receive_packets_confirmed_total{dst_chain="ibc-1",dst_channel="channel-0",dst_port="transfer",service_name="unknown_service",src_chain="ibc-0",src_channel="channel-0",src_port="transfer",otel_scope_name="hermes",otel_scope_version=""} 1
# HELP send_packet_events_total Number of SendPacket events received
# TYPE send_packet_events_total counter
send_packet_events_total{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
send_packet_events_total{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 4
# HELP timeout_events_total Number of TimeoutPacket events received
# TYPE timeout_events_total counter
timeout_events_total{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
timeout_events_total{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
# HELP timeout_packets_confirmed_total Number of confirmed timeout packets. Available if relayer runs with Tx confirmation enabled
# TYPE timeout_packets_confirmed_total counter
timeout_packets_confirmed_total{dst_chain="ibc-0",dst_channel="channel-0",dst_port="transfer",service_name="unknown_service",src_chain="ibc-1",src_channel="channel-0",src_port="transfer",otel_scope_name="hermes",otel_scope_version=""} 0
timeout_packets_confirmed_total{dst_chain="ibc-1",dst_channel="channel-0",dst_port="transfer",service_name="unknown_service",src_chain="ibc-0",src_channel="channel-0",src_port="transfer",otel_scope_name="hermes",otel_scope_version=""} 0
# HELP tx_latency_confirmed The latency for all transactions submitted & confirmed to a specific chain, i.e. the difference between the moment when Hermes received a batch of events until the corresponding transaction(s) were confirmed. Milliseconds.
# TYPE tx_latency_confirmed histogram
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="1000"} 0
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="5000"} 0
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="9000"} 2
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="13000"} 2
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="17000"} 2
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="20000"} 2
tx_latency_confirmed_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="+Inf"} 2
tx_latency_confirmed_sum{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 11980
tx_latency_confirmed_count{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 2
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="1000"} 0
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="5000"} 0
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="9000"} 1
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="13000"} 1
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="17000"} 1
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="20000"} 1
tx_latency_confirmed_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="+Inf"} 1
tx_latency_confirmed_sum{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 6021
tx_latency_confirmed_count{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 1
# HELP tx_latency_submitted The latency for all transactions submitted to a specific chain, i.e. the difference between the moment when Hermes received a batch of events and when it submitted the corresponding transaction(s). Milliseconds.
# TYPE tx_latency_submitted histogram
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="200"} 0
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="500"} 2
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="1000"} 2
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="2000"} 2
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="5000"} 2
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="10000"} 2
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="+Inf"} 2
tx_latency_submitted_sum{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 599
tx_latency_submitted_count{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 2
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="200"} 0
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="500"} 1
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="1000"} 2
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="2000"} 2
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="5000"} 2
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="10000"} 2
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="+Inf"} 2
tx_latency_submitted_sum{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 837
tx_latency_submitted_count{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 2
# HELP wallet_balance The balance of each wallet Hermes uses per chain. Please note that when converting the balance to f64 a loss in precision might be introduced in the displayed value
# TYPE wallet_balance gauge
wallet_balance{account="cosmos1340jyu3hawjzusu4jfwh29prpglkju5rlkpesn",chain="ibc-1",denom="stake",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 99994729
wallet_balance{account="cosmos1fk5ykcvkgr4yzlzfyegnaaqyc0ulv8wv8u9hjl",chain="ibc-3",denom="stake",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 100000000
wallet_balance{account="cosmos1j6z6q9d2gf2suav88z8g3zf726vz9ehg4hkr8x",chain="ibc-0",denom="stake",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 99993392
wallet_balance{account="cosmos1yxzuet72f4qlks8tzrna6y2q4wchur02gqs5al",chain="ibc-2",denom="stake",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 100000000
# HELP workers Number of workers
# TYPE workers gauge
workers{service_name="unknown_service",type="packet",otel_scope_name="hermes",otel_scope_version=""} 2
workers{service_name="unknown_service",type="wallet",otel_scope_name="hermes",otel_scope_version=""} 4
# HELP ws_events_total How many IBC events did Hermes receive via the websocket subscription
# TYPE ws_events_total counter
ws_events_total{chain="ibc-0",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 17
ws_events_total{chain="ibc-1",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 15
ws_events_total{chain="ibc-2",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 9
ws_events_total{chain="ibc-3",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 9
# HELP ws_reconnect_total Number of times Hermes reconnected to the websocket endpoint
# TYPE ws_reconnect_total counter
ws_reconnect_total{chain="ibc-0",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
ws_reconnect_total{chain="ibc-1",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
ws_reconnect_total{chain="ibc-2",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
ws_reconnect_total{chain="ibc-3",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version=""} 0
```
