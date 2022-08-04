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

1. Is Hermes active (i.e., *submitting* any transactions to any network)?
2. Are Hermes transactions successful (i.e., *confirmed* and included in the network)?
3. What is the overall IBC status of each network?
4. How efficient and how secure is the IBC status on each network?

For each of this question, there is a dedicated sub-section:

<!-- toc -->


## Is Hermes active?

By _active_ we mean specifically: is Hermes *submitting* any transactions to any network?
The metrics in the table below are design to answer this question on multiple dimensions.

| Name                       | Description                                                                                                                                                                 | OpenTelemetry type  |
| -------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------- |
| `workers`                  | Number of workers per type                                                                                                                                                  | `i64` UpDownCounter |
| `client_updates_submitted` | Number of client update messages submitted, per chain and client                                                                                                            | `u64` Counter       |
| `wallet_balance`           | The balance of each wallet Hermes uses per chain                                                                                                                            | `f64` ValueRecorder |
| `tx_latency_submitted`     | Latency for all transactions submitted to a chain | `u64` ValueRecorder |
| `total_messages_submitted` | Number of messages submitted to a specific chain                                                                                                                            | `u64` Counter       |

Notes & more details below:

**What is a worker?**
  * A worker is a separate thread of execution and there are five types of workers:
    * `Client`: The worker that refreshed a client periodically and detects misbehaviour.
    * `Connection`: The worker that handles connection open handshake that may be incomplete.
    * `Channel`: The worker that handles channel open handshake that may be incomplete.
    * `Packet`: The worker that handles packet relaying.
    * `Wallet`: The worker that periodically queries for the balance of each wallet that Hermes is using and updates `wallet_balance` metric.
  * For example, if your metrics show that you have 0 packet workers (`workers{type="packet"} 0`), that is a clear indication that Hermes is *not relaying any packets at the moment*.

**How do we define the latency of a submitted transaction?**
The latency is defined as the difference between the moment when Hermes received an event (through the websocket) until the moment when the corresponding transaction(s) were submitted
into a full node's mempool.
- If a transaction is submitted it does not mean it was confirmed, see below for more details.
- This metric is tracked per chain, counterparty chain, channel and port.


**A note on wallet balances.**
For the `wallet_balance`, we convert from a String into a f64, which can lead to a loss in precision in the displayed value.


## Are Hermes transactions successful?

This table shows the metrics for Hermes performance.
Importantly, these metrics are only displayed if the configuration `tx_confirmation = true` is set in your config.toml.

| Name                               | Description                                                                                                                                                              | OpenTelemetry type  |
| ---------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------- |
| `tx_latency_confirmed`             | Latency for all transactions confirmed by a chain | `u64` ValueRecorder |
| `receive_packets_confirmed`        | Number of confirmed receive packets, per chain, channel and port                                                                                                         | `u64` Counter       |
| `acknowledgment_packets_confirmed` | Number of confirmed acknowledgment packets, per chain, channel and port                                                                                                  | `u64` Counter       |
| `timeout_packets_confirmed`        | Number of confirmed timeout packets, per chain, channel and port                                                                                                         | `u64` Counter       |

**How do we define the latency of a confirmed transaction?**
This is the difference between the moment when Hermes received an event until the corresponding transaction(s) were confirmed.
- Similarly to `tx_latency_submitted`, this metrics is tracked per chain, counterparty chain, channel and port.
- This metrics usually contains strictly larger values than `tx_latency_submitted`, because Hermes first submits transactions into the network's mempool,
and then it takes some more time elapses until the network includes those transactions in a block.

## What is the overall IBC status of each network?

These metrics are not specific to your Hermes instance. These are metrics that capture the activity of _all IBC relayers_.

> Important:
> You Hermes instance produces these metrics based on the *events* it receives via a websocket to the full nodes of each network.
> If these events are not being updated, that is a good indication that either:
>   - The network has no IBC activity, or
>   - The websocket connection to that network is broken.

| Name                       | Description                                                    | OpenTelemetry type  |
| -------------------------- | -------------------------------------------------------------- | ------------------- |
| `send_packet_events`       | Number of SendPacket events received                           | `u64` Counter       |
| `acknowledgement_events`   | Number of WriteAcknowledgement events received                 | `u64` Counter       |
| `timeout_events`           | Number of TimeoutPacket events received                        | `u64` Counter       |
| `backlog_oldest_sequence`  | Sequence number of the oldest SendPacket event in the backlog  | `u64` ValueRecorder |
| `backlog_oldest_timestamp` | Local timestamp for the oldest SendPacket event in the backlog | `u64` ValueRecorder |
| `backlog_size`             | Total number of SendPacket events in the backlog               | `u64` ValueRecorder |


**A note on the backlog metrics.**

This table shows the metrics which serve the purpose of understanding if Hermes is able to retrieve information from the chains:

| Name                           | Description                                                                        | OpenTelemetry type |
| ------------------------------ | ---------------------------------------------------------------------------------- | ------------------ |
| `ws_events`                    | Number of events Hermes received via the websocket subscription, per chain         | `u64` Counter      |
| `ws_reconnect`                 | Number of times Hermes reconnected to the websocket endpoint, per chain            | `u64` Counter      |
| `queries`                      | Number of queries submitted by Hermes, per chain and query type                    | `u64` Counter      |

## Efficiency & security concerns

This table shows the metrics which serve the purpose of understanding the efficiency of Hermes:

| Name                           | Description                                                                                                                                                                 | OpenTelemetry type  |
| ------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------- |
| `queries`                      | Number of queries submitted by Hermes, per chain and query type                                                                                                             | `u64` Counter       |
| `queries_cache_hits`           | Number of cache hits for queries submitted by Hermes, per chain and query type                                                                                              | `u64` Counter       |
| `tx_latency_submitted`         | Latency for all transactions submitted to a chain (i.e., difference between the moment when Hermes received an event until the corresponding transaction(s) were submitted), per chain, counterparty chain, channel and port | `u64` ValueRecorder |
| `cleared_send_packet_count`    | Number of SendPacket events received during the initial and periodic clearing, per chain, counterparty chain, channel and port                                              | `u64` Counter       |
| `cleared_acknowledgment_count` | Number of WriteAcknowledgement events received during the initial and periodic clearing, per chain, counterparty chain, channel and port                                    | `u64` Counter       |



This table shows the metrics which serve the purpose of understanding the security status:

| Name                             | Description                                                                                   | OpenTelemetry type |
| -------------------------------- | --------------------------------------------------------------------------------------------- | ------------------ |
| `client_misbehaviours_submitted` | Number of misbehaviours detected and submitted, per sending chain, receiving chain and client | `u64` Counter      |


Notes:
* `queries` and `queries_cache_hits` values are complementary. For the total number of queries, the two metrics should be summed for a specific query type.
* The metric `client_misbehaviours_submitted` is disabled if `misbehaviour = false` in your Hermes config.toml.
