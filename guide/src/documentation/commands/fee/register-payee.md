# Register Payee

Use this command in order to specify the address which will receive the `ack_fee` and `timeout_fee` from incentivised packets relayed by the specified chain on the specified channel. By default this is the address of the reverse relayer's wallet.

__WARNING:__ Use this command with caution as some chains do not allow relayer address and payee to be equal. So reverting the payee address to the relayer address might be difficult after using this command.

```shell
{{#include ../../../templates/help_templates/fee/register-payee.md}}
```

__Example__

Register the address `cosmos10h9stc5v6ntgeygf5xf945njqq5h32r53uquvw` for the chain `ibc-1` on channel `channel-0`:

```shell
{{#template ../../../templates/commands/hermes/fee/register-payee_1.md CHAIN_ID=ibc-1 CHANNEL_ID=channel-0 PORT_ID=transfer PAYEE_ADDRESS=cosmos10h9stc5v6ntgeygf5xf945njqq5h32r53uquvw}}
```

```json
SUCCESS Successfully registered payee
```