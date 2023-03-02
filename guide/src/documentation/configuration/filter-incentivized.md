# Filter incentivized packets

Hermes can be configured in order to only relay packets which are incentivized. This is done by using the `[[chain.packet_filter.min_fee]]` configuration.

When this filter is configured, Hermes will not relay ignore `send_packet` events when they do not meet the configured requirements. This configuration can be set to be per channel or for a set of channels using regular expression.

## Examples

___Channel, amount and denom specific___

This example will configure Hermes so it will ignore `send_packet` events from `channel-0` which do not have at least `10 uatoms` as the `recv_fee`.

```
[chains.packet_filter.min_fees.'channel-0']
  recv    = [{ amount = 10, denom = 'uatom' }]
```

___Amount and denom specific___

This example will configure Hermes so it will ignore `send_packet` events from any channel which do not have at least `10 uatoms` as the `recv_fee`.

```
[chains.packet_filter.min_fees.'*']
  recv    = [{ amount = 10, denom = 'uatom' }]
```

___Amount only___

This example will configure Hermes so it will ignore `send_packet` events from any channel which do not have at least 10 of any token as the `recv_fee`.

```
[chains.packet_filter.min_fees.'*']
  recv    = [{ amount = 10 }]
```

___Multiple filters___

This example will configure Hermes so it will ignore `send_packet` events from any channel which starts with `ics`, does not have at least `10 uatom`, `20 stake` or 50 of any token as the `recv_fee`.

```
[chains.packet_filter.min_fees.'ics*']
  recv    = [{ amount = 10, denom = 'uatom' }, { amount = 20, denom = 'stake' }, { amount = 50}]
```
