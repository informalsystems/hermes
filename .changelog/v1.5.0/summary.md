*May 24th, 2023*

🎉 **Hermes v1.5.0** is here, packed with a slew of exciting updates, including
breaking changes💥, brand-new features🎁, performance enhancements🚀, and
sweeping improvements✨. 

The one breaking change is the removal of the `unbonding_period` setting
from the chain configuration. This is now replaced by a fresh
`ccv_consumer_chain` flag for Cross-Chain Validation (CCV) consumer chains. 

Also, Hermes has strengthened its misbehavior detection. With the
`mode.misbehaviour.enabled` setting enabled (now the case by default)
the relayer will closely monitor on-chain client updates, comparing submitted
headers with those fetched from its RPC node. In the event of any discrepancy,
Hermes will submit a `MisbehaviourMsg` to the chain hosting the IBC client
and provide the evidence to the reference chain.

This version rolls out a string of performance enhancements. Event batches
are now delivered after a configurable delay, greatly trimming down latency
when relaying, particularly on high-traffic channels. This can be adjusted
using the `batch_delay` setting in the per-chain configuration. Plus, packet
acknowledgments are only queried when there are packet commitments on the
counterparty, resulting in a major speed boost for packet clearing and
on-start scanning! 🚀

In addition, the `trusted_node` setting can now specify whether the full node
Hermes connects to is trusted or not. If untrusted, the light client will
verify headers included in the `ClientUpdate` message.
However, a word of caution: configuring the full node as trusted may cut
down latency but could risk sending invalid client updates to the chain. Use wisely! ⚠️

Our [Hermes guide](https://hermes.informal.systems/) has been re-organized a bit,
now featuring a new [*Performance Tuning*][perf-guide] page that details the
settings for optimizing the performance of the relayer.

For all the debuggers out there, Hermes now equips a new `--debug` global
flag with several selectable values, and two bonus flags, `--archive-address`
and `--restart-height` that enable a client update following a genesis restart
without an IBC upgrade proposal.

When it comes to telemetry, the destination chain is now added to the labels of
the confirmed packet metrics 📊. Take note that some metrics now have the
suffix `_total`. If you're using a running Grafana dashboard or any other tool
relying on the metric labels, an update might be needed.
The [corresponding page in the guide][telemetry-guide] reflects the new metric
labels for your convenience.

There's also a fresh configuration option to specify the directory used for the
keyring store.

From this version onwards, multi-platform (arm64 and amd64) images will be
distributed both on Docker Hub and the GitHub Content Repository.

[perf-guide]: https://hermes.informal.systems/documentation/configuration/performance.html
[telemetry-guide]: https://hermes.informal.systems/documentation/telemetry/operators.html

