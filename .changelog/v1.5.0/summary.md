*May 24th, 2023*

Hermes v1.5.0 brings several significant updates, including breaking changes, features, performance enhancements, and improvements.

One notable breaking change is the removal of the `unbonding_period` setting from the chain configuration.
It is replaced by a new `ccv_consumer_chain` flag for Cross-Chain Validation (CCV) consumer chains.

Hermes has also bolstered misbehavior detection. If the `mode.misbehaviour.enabled` setting is set to `true`,
which is now the default, the software will now monitor on-chain client updates, comparing the submitted
headers with those it obtains from its RPC node. In case of any discrepancy, Hermes will submit a `MisbehaviourMsg`
to the chain hosting the IBC client and present the evidence to the reference chain.

This version also introduces a series of performance enhancements. Event batches are now emitted after a
configurable delay, substantially reducing latency when relaying, especially on high traffic channels.
This is adjustable through the `batch_delay` setting in the per-chain configuration.
Additionally, packet acknowledgments are now only queried when there are packet commitments on the counterparty,
which substantially speeds up packet clearing and on-start scanning.

Furthermore, the `trusted_node` setting can now be used to specify if the full node Hermes connects to is trusted.
If untrusted, the light client will verify headers included in the `ClientUpdate` message.
However, it's crucial to note that configuring the full node as trusted may reduce latency but could lead to sending
invalid client updates to the chain, and hence should be used judiciously.

The [Hermes guide](https://hermes.informal.systems/documentation/configuration/performance.html) has been re-organized,
and now features a new [*Performance Tuning*]() page, which documents the settings to be used to tweak the performance characteristics of the relayer.

Hermes now also provides a new `--debug` global flag with several selectable values, and two optional flags,
`--archive-address` and `--restart-height` that permit a client update following a genesis restart without an IBC upgrade proposal.

For telemetry, the destination chain was added to the labels of the confirmed packet metrics.
Please note that some metrics now contain the suffix `_total`. If you have a running Grafana dashboard or any other tool
using the metric labels you might need to update them.
The [corresponding page in the guide](https://hermes.informal.systems/documentation/telemetry/operators.html) has been
updated in order to reflect the new metric labels.

A new configuration option was also added to specify the directory used for the keyring store. 

As of this version, multi-platform (arm64 and amd64) images will be published to both Docker Hub and the GitHub Content Repository. 
