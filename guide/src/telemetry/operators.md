# Hermes operators guide to using metrics

This section is a basic guide on how Hermes metrics can be used to observe both
the current state of the Hermes relayer and the networks it is connected to.

## General remarks about the metrics

- All Hermes metrics are tracked and updated from the moment the Hermes service (i.e., `start`) starts up.
Metrics are automatically reset if the service is restarted.
- For maximum reliability, it is advised to combine monitoring of your Hermes service with monitoring of your full nodes.
- TODO: Grafana template here.

## Table of Contents

Hermes metrics are designed to be able to answer four basic questions:

1.

<!-- toc -->


## Hermes activity

This table shows the metrics which serve the purpose of understanding if Hermes is active and correctly interacting with the chains:

| Name                       | Description                                                                                                                                                                 | OpenTelemetry type  |
| -------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------- |
| `workers`                  | Number of workers per type                                                                                                                                                  | `i64` UpDownCounter |
| `client_updates_submitted` | Number of client update messages submitted, per chain and client                                                                                                            | `u64` Counter       |
| `wallet_balance`           | The balance of each wallet Hermes uses per chain                                                                                                                            | `f64` ValueRecorder |
| `tx_latency_submitted`     | Latency for all transactions submitted to a chain (i.e., difference between the moment when Hermes received an event until the corresponding transaction(s) were submitted), per chain, counterparty chain, channel and port | `u64` ValueRecorder |
| `total_messages_submitted` | Number of messages submitted to a specific chain                                                                                                                            | `u64` Counter       |

Notes:

* For the `wallet_balance` please note that when converting the balance to f64 a loss in precision might be introduced in the displayed value.
* What is a worker ? A worker is a separate thread of execution and there are five types of workers:
  * Client: The worker that refreshed a client periodically and detects misbehaviour.
  * Connection: The worker that handles connection open handshake that may be pending.
  * Channel: The worker that handles channel open handshake that may be pending.
  * Packet: The worker that handles packet relaying.
  * Wallet: The worker that periodically queries for the balance of each wallet that Hermes is using and updates `wallet_balance` [Prometheus][prometheus] metric.

## Tx confirmation

This table shows the metrics for Hermes performance. These metrics are only shown if the configuration `tx_confirmation = true` is set:

| Name                               | Description                                                                                                                                                              | OpenTelemetry type  |
| ---------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------- |
| `tx_latency_confirmed`             | Latency for all transactions confirmed by a chain (i.e., difference between the moment when Hermes received an event until the corresponding transaction(s) were confirmed), per chain, counterparty chain, channel and port | `u64` ValueRecorder |
| `receive_packets_confirmed`        | Number of confirmed receive packets, per chain, channel and port                                                                                                         | `u64` Counter       |
| `acknowledgment_packets_confirmed` | Number of confirmed acknowledgment packets, per chain, channel and port                                                                                                  | `u64` Counter       |
| `timeout_packets_confirmed`        | Number of confirmed timeout packets, per chain, channel and port                                                                                                         | `u64` Counter       |

## Hermes connectivity to a network

This table shows the metrics which serve the purpose of understanding if Hermes is able to retrieve information from the chains:

| Name                           | Description                                                                        | OpenTelemetry type |
| ------------------------------ | ---------------------------------------------------------------------------------- | ------------------ |
| `ws_events`                    | Number of events Hermes received via the websocket subscription, per chain         | `u64` Counter      |
| `ws_reconnect`                 | Number of times Hermes reconnected to the websocket endpoint, per chain            | `u64` Counter      |
| `queries`                      | Number of queries submitted by Hermes, per chain and query type                    | `u64` Counter      |

## Live network activity

These metrics are all per chain, counterparty chain, channel and port:

| Name                       | Description                                                    | OpenTelemetry type  |
| -------------------------- | -------------------------------------------------------------- | ------------------- |
| `send_packet_events`       | Number of SendPacket events received                           | `u64` Counter       |
| `acknowledgement_events`   | Number of WriteAcknowledgement events received                 | `u64` Counter       |
| `timeout_events`           | Number of TimeoutPacket events received                        | `u64` Counter       |
| `backlog_oldest_sequence`  | Sequence number of the oldest SendPacket event in the backlog  | `u64` ValueRecorder |
| `backlog_oldest_timestamp` | Local timestamp for the oldest SendPacket event in the backlog | `u64` ValueRecorder |
| `backlog_size`             | Total number of SendPacket events in the backlog               | `u64` ValueRecorder |

## Efficiency

This table shows the metrics which serve the purpose of understanding the performance of Hermes:

| Name                           | Description                                                                                                                                                                 | OpenTelemetry type  |
| ------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------- |
| `queries`                      | Number of queries submitted by Hermes, per chain and query type                                                                                                             | `u64` Counter       |
| `queries_cache_hits`           | Number of cache hits for queries submitted by Hermes, per chain and query type                                                                                              | `u64` Counter       |
| `tx_latency_submitted`         | Latency for all transactions submitted to a chain (i.e., difference between the moment when Hermes received an event until the corresponding transaction(s) were submitted), per chain, counterparty chain, channel and port | `u64` ValueRecorder |
| `cleared_send_packet_count`    | Number of SendPacket events received during the initial and periodic clearing, per chain, counterparty chain, channel and port                                              | `u64` Counter       |
| `cleared_acknowledgment_count` | Number of WriteAcknowledgement events received during the initial and periodic clearing, per chain, counterparty chain, channel and port                                    | `u64` Counter       |

Remarks:

* `queries` and `queries_cache_hits` values are complementary. For the total number of queries, the values should be summed for a specific query type.

## Security

This table shows the metrics which serve the purpose of understanding the security status:

| Name                             | Description                                                                                   | OpenTelemetry type |
| -------------------------------- | --------------------------------------------------------------------------------------------- | ------------------ |
| `client_misbehaviours_submitted` | Number of misbehaviours detected and submitted, per sending chain, receiving chain and client | `u64` Counter      |