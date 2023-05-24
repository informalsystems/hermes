# Performance Tuning

## Overview

Hermes provides several configuration options that users can tweak to optimize its performance to suit specific requirements. This guide provides an overview of these options, and suggests ways to modify them for different scenarios.

The two per-chain configuration options you can use to tune the performance of Hermes as of version 1.5 are `trusted_node` and `batch_delay`.

## Configuration Options

### 1. Trusted Node

The `trusted_node` setting is an experimental option that determines whether or not the full node is trusted.

```toml
trusted_node = false
```

When set to `true`, Hermes trusts the full node and does not verify headers included in the `ClientUpdate` message using the light client. This could lead to faster processing as it bypasses the verification step.

However, it's important to note that when the full node is configured as trusted, the verification traces will not be provided. This could potentially lead to failure in client updates after a significant change in validator sets.

If you prefer security over speed, or if the validator set changes frequently, consider leaving this setting as `false`, which is also the default.

### 2. Batch Delay

The `batch_delay` setting dictates the delay until an event batch is emitted if no `NewBlock` events have been received yet.

```toml
batch_delay = '500ms'
```

Lower `batch_delay` values will result in faster event processing, improving the latency of Hermes. However, setting it too low could cause some events to be missed. Conversely, higher values will increase the latency of Hermes, but it is less likely to miss any events.

If you prioritize processing speed and can tolerate the occasional missed event, consider setting a lower `batch_delay`. For critical applications where no event should be missed, consider a higher `batch_delay`.

The default `500ms` provides a good balance between speed and reliability, while being very unlikely to miss any events.

## Conclusion

The tuning of Hermes performance relies on the balance between processing speed and reliability. Keep in mind that tuning these configurations according to your needs could significantly improve the performance of your Hermes instance. Please thoroughly test any changes in a controlled environment before implementing them in a production setting. 

Remember, every blockchain and network has unique characteristics that can affect the performance of the relayer, so there's no one-size-fits-all configuration. Feel free to experiment and fine-tune these settings to achieve optimal performance for your specific use case.
