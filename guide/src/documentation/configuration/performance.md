# Performance tuning

## Table of contents
<!-- toc -->

## Overview

Hermes provides several configuration options that users can tweak to optimize its performance to suit specific requirements. This guide provides an overview of these options, and suggests ways to modify them for different scenarios.

The two per-chain configuration options you can use to tune the performance of Hermes as of version 1.5 are `trusted_node` and `batch_delay`.

## Configuration Options

### 1. Trusted Node

The `trusted_node` setting is an experimental option that determines whether or not the full node is trusted.

```toml
trusted_node = false
```

When set to `true`, Hermes trusts the full node and does not verify headers included in the `ClientUpdate` message using the light client.
This could lead to faster processing as it bypasses the verification step.

However, it's important to note that when the full node is configured as trusted, the verification traces will not be provided.
This could potentially lead to failure in client updates after a significant change in validator sets.

If you prefer security over speed, or if the validator set changes frequently, consider leaving this setting as `false`, which is also the default.

### 2. Batch Delay

The `batch_delay` setting dictates the delay until an event batch is emitted if no `NewBlock` events have been received yet.

```toml
batch_delay = '500ms'
```

Lower `batch_delay` values will result in faster event processing, improving the latency of Hermes.
However, setting it too low could sometimes cause events to be split across more batches than necessary, which will then cause Hermes to send more client updates than otherwise required.
Conversely, higher values will increase the latency of Hermes, but will minimize the number of client updates.

If you prioritize processing speed and can tolerate the potentially slightly higher costs, consider setting a lower `batch_delay`. For backup relayer or settings where latency is not as important, consider a higher `batch_delay`.

The default `500ms` provides a good balance between speed and reliability, while still minimizing the number of client updates to send.

### 3. Slow start

On blochains with many open channels, connections and/or clients, Hermes may take a long while to start.
That is because Hermes needs to perform a scan of all available clients, connections and channels on that blockchain in order to refresh these clients, complete the handshakes of partially open channels and connections.
If Hermes takes more than a couple minutes to start, that may be because there are too many clients, connections and/or channels.

To alleviate this issue, there are two potential solutions:

#### 3.1 Specify an allow list in the packet filter

Add the end of the `[[chains]]` section for affected blockchain, you can specify a packet filter with an allow list.
This will ensure Hermes will only scan for the listed channels, and gather the corresponding connections and clients for these channels only.

For example, to only relay on two channels named `channel-0` and `channel-1`, on port `transfer`, you can add the following packet filter:

```toml
 [chains.packet_filter]
 policy = 'allow'
 list = [
   ['transfer', 'channel-0'],
   ['transfer', 'channel-1'],
 ]
```

**Caveat:** the allow list cannot contain any wildcards, otherwise Hermes will have to perform a full scan to
gather all channels and subsequently filter them against the allow list.

For example, the following configuration would cause Hermes to perform such a full scan, and therefore potentially slow down its startup time:

```toml
 [chains.packet_filter]
 policy = 'allow'
 list = [
   ['ica*', '*'],
   ['transfer', 'channel-0'],
 ]
```

#### 3.2 Disable clients, connections, channels workers and packet clearing on startup

If you wish to relay on all channels, or to use wildcards in the packet filter, then another option to speed up the startup is to disable
scanning altogether.

At the moment, there is no single setting to do this, but by disabling the clients, connections and channels workers and
setting `clear_on_start` to `false` under the `mode.packets` section, Hermes will not need to perform a scan and will only
relay packets on active channels, provided they match the packet filter, if present. Otherwise Hermes will relay on all
active channels.

Please note that because these settings are global, they will affect the behaviour of Hermes for all chains listed in its configuration.

Here is how the configuration file should look like in order to disable scanning altogether.

```toml
# ...

[mode.clients]
enabled = false

# ...

[mode.connections]
enabled = false

# ...

[mode.channels]
enabled = false

# ...

[mode.packets]
enabled = true
clear_on_start = false
```

## Conclusion

The tuning of Hermes performance relies on the balance between processing speed and reliability. Keep in mind that tuning these configurations according to your needs could significantly improve the performance of your Hermes instance. Please thoroughly test any changes in a controlled environment before implementing them in a production setting. 

Remember, every blockchain and network has unique characteristics that can affect the performance of the relayer, so there's no one-size-fits-all configuration. Feel free to experiment and fine-tune these settings to achieve optimal performance for your specific use case.
