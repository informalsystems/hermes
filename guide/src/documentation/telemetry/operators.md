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
5. Am I getting fee rewards from ICS29 incentivized packets?

For each of this question, there is a dedicated subsection:

<!-- toc -->


## Is Hermes active?

By _active_, we mean specifically: is Hermes *submitting* any transactions to any network?
The metrics in the table below are design to answer this question on multiple dimensions.

| Name                       | Description                                                                                                                                                                 | OpenTelemetry type  | Configuration Dependencies |
| -------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------- | -------------------------- |
| `workers`                  | Number of workers per type                                                                                                                                                  | `i64` UpDownCounter | Corresponding workers enabled |
| `client_updates_submitted_total` | Number of client update messages submitted, per sending chain, receiving chain and client                                                                                                            | `u64` Counter       | Client, Connection, Channel or Packet workers enabled |
| `client_updates_skipped_total` | Number of client update messages skipped because the consensus state already exists, per sending chain, receiving chain and client                                                                                                            | `u64` Counter       | Client, Connection, Channel or Packet workers enabled |
| `wallet_balance`           | The balance of each wallet Hermes uses per chain                                                                                                                            | `f64` ValueRecorder | None                       |
| `tx_latency_submitted`     | Latency for all transactions submitted to a chain | `u64` ValueRecorder | None                       |
| `messages_submitted_total` | Number of messages submitted to a specific chain                                                                                                                            | `u64` Counter       | None                       |

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

**latency histogram**
The `tx_latency_submitted` and `tx_latency_confirmed` are displayed with histogram buckets which each contain the number of values less or equal to their bucket label. This means that if there are 5 buckets with label `500`, `2000`, `3000`, `4000` and `5000` and 2 `tx_latency_submitted` were recorded of respectively `1800ms` and `3100ms` then the `tx_latency_submitted` will look like this:

```text
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="500"} 0
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="2000"} 1
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="3000"} 1
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="4000"} 2
tx_latency_submitted_bucket{chain="ibc-0",channel="channel-0",counterparty="ibc-1",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="5000"} 2
tx_latency_submitted_bucket{chain="ibc-1",channel="channel-0",counterparty="ibc-0",port="transfer",service_name="unknown_service",otel_scope_name="hermes",otel_scope_version="",le="+Inf"} 2
```
The range of the buckets can be configured using the `latency_submitted` and `latency_confirmed` seen [here](./index.md)


## Are Hermes transactions successful?

This table shows the metrics for Hermes performance.
Importantly, these metrics are only displayed if the configuration `tx_confirmation = true` is set in your config.toml.

| Name                               | Description                                                                                                                                                              | OpenTelemetry type  | Configuration Dependencies |
| ---------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------- | -------------------------- |
| `tx_latency_confirmed`             | Latency for all transactions confirmed by a chain | `u64` ValueRecorder | Transaction confirmation enabled |
| `receive_packets_confirmed_total`        | Number of confirmed receive packets, per chain, channel and port                                                                                                         | `u64` Counter       | Packet workers enabled, and Transaction confirmation enabled |
| `acknowledgment_packets_confirmed_total` | Number of confirmed acknowledgment packets, per chain, channel and port                                                                                                  | `u64` Counter       | Packet workers enabled, and Transaction confirmation enabled |
| `timeout_packets_confirmed_total`        | Number of confirmed timeout packets, per chain, channel and port                                                                                                         | `u64` Counter       | Packet workers enabled and Transaction confirmation enabled |

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
| `send_packet_events_total`           | Number of SendPacket events received                                               | `u64` Counter      | Packet workers enabled     |
| `acknowledgement_events_total`       | Number of WriteAcknowledgement events received                                     | `u64` Counter      | Packet workers enabled     |
| `timeout_events_total`               | Number of TimeoutPacket events received                                            | `u64` Counter      | Packet workers enabled     |
| `ws_events_total`                    | Number of events Hermes (including `send_packet`, `acknowledgment`, and `timeout`) received via the websocket subscription, per chain         | `u64` Counter      | None                       |
| `ws_reconnect_total`                 | Number of times Hermes reconnected to the websocket endpoint, per chain            | `u64` Counter      | None                       |
| `queries_total`                      | Number of queries submitted by Hermes, per chain and query type                    | `u64` Counter      | None                       |

Notes:

- Except for `ws_reconnect_total`, all these metrics should typically increase regularly in the common-case. That is an indication that the network is regularly producing new blocks and there is ongoing IBC activity, eg `send_packet`, `acknowledgment`, and `timeout`.
- The metric `ws_reconnect_total` signals that the websocket connection was broken and Hermes had to re-establish that. It is usually an indication that your full node may be falling behind or is experiencing instability.

Since Hermes v1, we also introduced 3 metrics that sketch the backlog status of IBC relaying.

| Name                       | Description                                                    | OpenTelemetry type  | Configuration Dependencies |
| -------------------------- | -------------------------------------------------------------- | ------------------- | -------------------------- |
| `backlog_oldest_sequence`  | Sequence number of the oldest SendPacket event in the backlog  | `u64` ValueRecorder | Packet workers enabled     |
| `backlog_latest_update_timestamp` | Local timestamp for the last time the backlog metrics have been updated | `u64` ValueRecorder | Packet workers enabled     |
| `backlog_size`             | Total number of SendPacket events in the backlog               | `u64` ValueRecorder | Packet workers enabled     |


Notes:

- The `backlog_size` defines how many IBC packets users sent and were not yet relayed (i.e., received on the destination network, or timed-out).
If this metric is increasing, it signals that the packet queue is increasing and there may be some errors in the Hermes logs that need your attention.
- The `backlog_latest_update_timestamp` is used to get information on the reliability of the `backlog_*` metrics. If the timestamp doesn't change it means there might be an issue with the metrics.
- __NOTE__: The Hermes instance might miss the acknowledgment of an observed IBC packets relayed, this will cause the `backlog_*` metrics to contain an invalid value. In order to minimise this issue, whenever the Hermes instance clears packets the `backlog_*` metrics will be updated using the queried pending packets.

## How efficient and how secure is the IBC status on each network?

| Name                           | Description                                                                                                                                                                 | OpenTelemetry type  | Configuration Dependencies |
| ------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------- | -------------------------- |
| `queries_total`                      | Number of queries submitted by Hermes, per chain and query type                                                                                                             | `u64` Counter       | None                       |
| `queries_cache_hits_total`           | Number of cache hits for queries submitted by Hermes, per chain and query type                                                                                              | `u64` Counter       | None                       |
| `tx_latency_submitted`         | Latency for all transactions submitted to a chain (i.e., difference between the moment when Hermes received an event until the corresponding transaction(s) were submitted), per chain, counterparty chain, channel and port | `u64` ValueRecorder | None                       |
| `cleared_send_packet_count_total`    | Number of SendPacket events received during the initial and periodic clearing, per chain, counterparty chain, channel and port                                              | `u64` Counter       | Packet workers enabled, and periodic packet clearing or clear on start enabled |
| `cleared_acknowledgment_count_total` | Number of WriteAcknowledgement events received during the initial and periodic clearing, per chain, counterparty chain, channel and port                                    | `u64` Counter       | Packet workers enabled, and periodic packet clearing or clear on start enabled |
| `broadcast_errors_total`        | Number of errors observed by Hermes when broadcasting a Tx, per error type and account                                                                                                         | `u64` Counter       | Packet workers enabled |
| `filtered_packets`        | Number of ICS-20 packets filtered because the memo and/or the receiver fields were exceeding the configured limits | `u64` Counter | Packet workers enabled, and `ics20_max_memo_size` and/or `ics20_max_receiver_size` enabled |

Notes:
- The two metrics `cleared_send_packet_count_total` and `cleared_acknowledgment_count_total` are only populated if `tx_confirmation = true`.
These two metrics usually correlate with `backlog_*` metrics. They are an indication that IBC packet relaying may be unsuccessful and that Hermes periodically
finds packets to clear (i.e., unblock).
- `queries_total` and `queries_cache_hits_total` values are complementary. For the total number of queries, the two metrics should be summed for a specific query type.

For security, we only expose one metric, described in the table below.
Note that this metrics is disabled if `misbehaviour = false` in your Hermes config.toml.

| Name                             | Description                                                                                   | OpenTelemetry type | Configuration Dependencies |
| -------------------------------- | --------------------------------------------------------------------------------------------- | ------------------ | -------------------------- |
| `client_misbehaviours_submitted_total` | Number of misbehaviours detected and submitted, per sending chain, receiving chain and client | `u64` Counter      | Client workers enabled and Clients misbehaviour detection enabled |

## Am I getting fee rewards?

| Name                | Description                                                                 | OpenTelemetry type  | Configuration Dependencies |
| ------------------- | --------------------------------------------------------------------------- | ------------------- | -------------------------- |
| `ics29_fee_amounts_total` | Total amount received from ICS29 fees                                       | `u64` Counter       | None                       |
| `ics29_period_fees` | Amount of ICS29 fees rewarded over the past 7 days type                     | `u64` ValueRecorder | None                       |

## Dynamic gas fees

The introduction of dynamic gas fees adds additional configuration which can be delicate to handle correctly. The following metrics can help correctly configure your relayer.

| Name                               | Description                                                          | OpenTelemetry type  | Configuration Dependencies |
| ---------------------------------- | -------------------------------------------------------------------- | ------------------- | -------------------------- |
| `dynamic_gas_queried_fees`         | The EIP-1559 base fee queried                                        | `u64` ValueRecorder | None                       |
| `dynamic_gas_queried_success_fees` | The EIP-1559 base fee successfully queried                           | `u64` ValueRecorder | None                       |
| `dynamic_gas_paid_fees`            | The EIP-1559 base fee paid                                           | `u64` ValueRecorder | None                       |

Notes:

- The `dynamic_gas_queried_fees` contains the gas price used after the query but before filtering by configured `max`. This means that this metric might contain the static gas price if the query failed.
- The `dynamic_gas_queried_success_fees` will only contain the gas price when the query succeeds, if this metric doesn't contain values or less values that the `dynamic_gas_queried_fees` this could indicate an issue with the endpoint used to query the fees.
- `dynamic_gas_paid_fees` will contain the price used by the relayer, the maximum value for this metric is `max`. If there are multiple values in the same bucket as the `max` it could indicate that the gas price queried is often higher than the configured `max`.