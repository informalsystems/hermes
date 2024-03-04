# Packet clearing

Hermes can be configured in order to clear packets which haven't been relayed. This can happen if there wasn't a relayer instance running when the packet event was submitted or if there was an issue relaying the packet.

There are four different configurations to determine when Hermes will clear packets.

## Global configurations

Two of these configurations are global to all chains and are in the `[mode.packet]` section.

### 1. `clear_on_start`

```toml
[mode.packet]
...
clear_on_start = true
```

This configuration is used to specify if Hermes should query and relay pending packets when starting the instance. If set this will only trigger once per running instance.

>__NOTE__: If this configuration is enabled Hermes will need to scan for channels as the pending packets will require the channel worker, refer to the [Slow start section](./performance.md#3-slow-start) for more information.

### 2. `clear_interval`

```toml
[mode.packet]
...
clear_interval = 100
```

This configuration defines how often Hermes will verify if there are pending packets and relay them. The value is the number of blocks observed, so the time between each clearing might very from chain to chain.

## Chain specific configuration

The third and fourth configurations are specific for each chain.

### 3. `clear_interval`

```toml
[[chains]]
...
clear_interval = 50
```

An additional `clear_interval` can be specified for each chain, this value is also in number of blocks. This configuration will override the clear interval value for the specific chain and can be used if chains need to have different clear values. This configuration is optional, if it is not set the global value will be used.

### 4. `excluded_sequences`

```toml
[[chains]]
...
excluded_sequences = [
    ['channel-0', [1, 2, 3]],
    ['channel-1', [4, 5, 6]]
]
```

It is possible to specify which packet sequences should be ignored when clearing packets for specific channels. This can be used when there are stuck packets which need to be handled in a specific way, but it is still required to clear the other stuck packets. This configuration will only filter packet when clearing, standard relaying will not filter the sequences configured in `excluded_sequences`.