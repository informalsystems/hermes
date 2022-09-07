# Hermes operators guide to using metrics

This section is a basic guide on how Hermes metrics can be used to observe both
the current state of the Hermes relayer and the networks it is connected to.

## General remarks about the metrics

- All Hermes metrics are tracked and updated from the moment the Hermes service (i.e., `start`) starts up.
Metrics are automatically reset if the service is restarted.
- For maximum reliability, it is advised to combine monitoring of your Hermes service with monitoring of your full nodes.
- Some metrics require specific configurations to be enabled, this is described in the `Configuration Dependencies` column.

## Table of Contents

Hermes' metrics are designed to be able to answer four basic questions:

1. Is Hermes active (i.e., *submitting* any transactions to any network)?
2. Are Hermes transactions successful (i.e., *confirmed* and included in the network)?
3. What is the overall IBC status of each network?
4. How efficient, and how secure is the IBC status on each network?

For each of this question, there is a dedicated subsection:

<!-- toc -->


## Is Hermes active?

By _active_, we mean specifically: is Hermes *submitting* any transactions to any network?
The metrics in the table below are design to answer this question on multiple dimensions.

| Name                       | Description                                                                                                                                                                 | OpenTelemetry type  | Configuration Dependencies |
| -------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------- | -------------------------- |
| `workers`                  | Number of workers per type                                                                                                                                                  | `i64` UpDownCounter | Corresponding workers enabled |
| `client_updates_submitted` | Number of client update messages submitted, per sending chain, receiving chain and client                                                                                                            | `u64` Counter       | Client, Connection, Channel or Packet workers enabled |
| `wallet_balance`           | The balance of each wallet Hermes uses per chain                                                                                                                            | `f64` ValueRecorder | None                       |
| `tx_latency_submitted`     | Latency for all transactions submitted to a chain | `u64` ValueRecorder | None                       |
| `total_messages_submitted` | Number of messages submitted to a specific chain                                                                                                                            | `u64` Counter       | None                       |

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

| Name                               | Description                                                                                                                                                              | OpenTelemetry type  | Configuration Dependencies |
| ---------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------- | -------------------------- |
| `tx_latency_confirmed`             | Latency for all transactions confirmed by a chain | `u64` ValueRecorder | Transaction confirmation enabled |
| `receive_packets_confirmed`        | Number of confirmed receive packets, per chain, channel and port                                                                                                         | `u64` Counter       | Packet workers enabled, and Transaction confirmation enabled |
| `acknowledgment_packets_confirmed` | Number of confirmed acknowledgment packets, per chain, channel and port                                                                                                  | `u64` Counter       | Packet workers enabled, and Transaction confirmation enabled |
| `timeout_packets_confirmed`        | Number of confirmed timeout packets, per chain, channel and port                                                                                                         | `u64` Counter       | Packet workers enabled and Transaction confirmation enabled |

**How do we define the latency of a confirmed transaction?**
This is the difference between the moment when Hermes received an event until the corresponding transaction(s) were confirmed.
- Similarly to `tx_latency_submitted`, this metrics is tracked per chain, counterparty chain, channel and port.
- This metrics usually contains strictly larger values than `tx_latency_submitted`, because Hermes first submits transactions into the network's mempool,
and then it takes some more time elapses until the network includes those transactions in a block.

## What is the overall IBC status of each network?

These metrics are not specific to your Hermes instance. These are metrics that capture the activity of _all IBC relayers_.

> ‼️ Important:
> Your Hermes instance produces these metrics based on the *events* it receives via a websocket to the full nodes of each network.
> If these events are not being updated, that is a good indication that either:
>   - The network has no IBC activity, or
>   - The websocket connection to that network is broken.

| Name                           | Description                                                                        | OpenTelemetry type | Configuration Dependencies |
| ------------------------------ | ---------------------------------------------------------------------------------- | ------------------ | -------------------------- |
| `send_packet_events`           | Number of SendPacket events received                                               | `u64` Counter      | Packet workers enabled     |
| `acknowledgement_events`       | Number of WriteAcknowledgement events received                                     | `u64` Counter      | Packet workers enabled     |
| `timeout_events`               | Number of TimeoutPacket events received                                            | `u64` Counter      | Packet workers enabled     |
| `ws_events`                    | Number of events Hermes (including `send_packet`, `acknowledgment`, and `timeout`) received via the websocket subscription, per chain         | `u64` Counter      | None                       |
| `ws_reconnect`                 | Number of times Hermes reconnected to the websocket endpoint, per chain            | `u64` Counter      | None                       |
| `queries`                      | Number of queries submitted by Hermes, per chain and query type                    | `u64` Counter      | None                       |

Notes:

- Except for `ws_reconnect`, all these metrics should typically increase regularly in the common-case. That is an indication that the network is regularly producing new blocks and there is ongoing IBC activity, eg `send_packet`, `acknowledgment`, and `timeout`.
- The metric `ws_reconnect` signals that the websocket connection was broken and Hermes had to re-establish that. It is usually an indication that your full node may be falling behind or is experiencing instability.

Since Hermes v1, we also introduced 3 metrics that sketch the backlog status of IBC relaying.

| Name                       | Description                                                    | OpenTelemetry type  | Configuration Dependencies |
| -------------------------- | -------------------------------------------------------------- | ------------------- | -------------------------- |
| `backlog_oldest_sequence`  | Sequence number of the oldest SendPacket event in the backlog  | `u64` ValueRecorder | Packet workers enabled     |
| `backlog_oldest_timestamp` | Local timestamp for the oldest SendPacket event in the backlog | `u64` ValueRecorder | Packet workers enabled     |
| `backlog_size`             | Total number of SendPacket events in the backlog               | `u64` ValueRecorder | Packet workers enabled     |


Notes:

- The `backlog_size` defines how many IBC packets users sent and were not yet relayed (i.e., received on the destination network, or timed-out).
If this metric is increasing, it signals that the packet queue is increasing and there may be some errors in the Hermes logs that need your attention.
- If the `backlog_oldest_sequence` remains unchanged for more than a few minutes, that means that the packet with the respective sequence number is likely blocked
and cannot be relayed. To understand for how long the packet is block, Hermes will populate `backlog_oldest_timestamp`  with the local time when it first observed
the `backlog_oldest_sequence` that is blocked.

## How efficient and how secure is the IBC status on each network?

| Name                           | Description                                                                                                                                                                 | OpenTelemetry type  | Configuration Dependencies |
| ------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------- | -------------------------- |
| `queries`                      | Number of queries submitted by Hermes, per chain and query type                                                                                                             | `u64` Counter       | None                       |
| `queries_cache_hits`           | Number of cache hits for queries submitted by Hermes, per chain and query type                                                                                              | `u64` Counter       | None                       |
| `tx_latency_submitted`         | Latency for all transactions submitted to a chain (i.e., difference between the moment when Hermes received an event until the corresponding transaction(s) were submitted), per chain, counterparty chain, channel and port | `u64` ValueRecorder | None                       |
| `cleared_send_packet_count`    | Number of SendPacket events received during the initial and periodic clearing, per chain, counterparty chain, channel and port                                              | `u64` Counter       | Packet workers enabled, and periodic packet clearing or clear on start enabled |
| `cleared_acknowledgment_count` | Number of WriteAcknowledgement events received during the initial and periodic clearing, per chain, counterparty chain, channel and port                                    | `u64` Counter       | Packet workers enabled, and periodic packet clearing or clear on start enabled |

Notes:
- The two metrics `cleared_send_packet_count` and `cleared_acknowledgment_count` are only populated if `tx_confirmation = true`.
These two metrics usually correlate with `backlog_*` metrics. They are an indication that IBC packet relaying may be unsuccessful and that Hermes periodically
finds packets to clear (i.e., unblock).
- `queries` and `queries_cache_hits` values are complementary. For the total number of queries, the two metrics should be summed for a specific query type.

For security, we only expose one metric, described in the table below.
Note that this metrics is disabled if `misbehaviour = false` in your Hermes config.toml.

| Name                             | Description                                                                                   | OpenTelemetry type | Configuration Dependencies |
| -------------------------------- | --------------------------------------------------------------------------------------------- | ------------------ | -------------------------- |
| `client_misbehaviours_submitted` | Number of misbehaviours detected and submitted, per sending chain, receiving chain and client | `u64` Counter      | Client workers enabled and Clients misbehaviour detection enabled |