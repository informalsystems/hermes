# Filter incentivized packets

Hermes can be configured in order to only relay packets which are incentivized. This is done by using the `[[chain.packet_filter.min_fees]]` setting.

When this filter is configured, Hermes will only relay `send_packet` events when they  meet the configured requirements. This configuration can be set per channel or for a set of channels using a wildcard expression.

> __WARNING__: This configuration is experimental. Packet clearing will be disabled for the channels which have a fee filter configured, and some `send_packet` events might not be relayed if the incentivized event is not in the same batch of events.

## Examples

___Channel, amount and denom specific___

This example will configure Hermes so it will ignore `send_packet` events from `channel-0` which do not have at least `10 uatoms` as the `recv_fee`.

```
[chains.packet_filter.min_fees.'channel-0']
  recv = [{ amount = 10, denom = 'uatom' }]
```

___Amount and denom specific___

This example will configure Hermes so it will ignore `send_packet` events from any channel which do not have at least `10 uatoms` as the `recv_fee`.

```
[chains.packet_filter.min_fees.'*']
  recv = [{ amount = 10, denom = 'uatom' }]
```

___Amount only___

This example will configure Hermes so it will only relay `send_packet` events sent with incentivized events.
```
[chains.packet_filter.min_fees.'*']
  recv    = [{ amount = 0 }]
```

___Multiple filters___

This example will configure Hermes so it will ignore `send_packet` events from any channel which starts with `ics`, does not have at least `10 uatom` or `20 stake` as the `recv_fee`.

```
[chains.packet_filter.min_fees.'ics*']
  recv    = [{ amount = 10, denom = 'uatom' }, { amount = 20, denom = 'stake' }]
```
