# Register Counterparty Payee

Use this command in order to specify the address which will receive the `recv_fee` from incentivised packets relayed by the specified chain on the specified channel.

__NOTE:__ Calling this command before starting the Hermes instance with the configuration `auto_register_counterparty_payee = true` set is useless as the `auto_register_counterparty_payee` will overwrite the address registered with the command.

```shell
{{#include ../../../templates/help_templates/fee/register-counterparty-payee.md}}
```

__Example__

Register the address `cosmos10h9stc5v6ntgeygf5xf945njqq5h32r53uquvw` for the chain `ibc-1` on channel `channel-0`:

```shell
{{#template ../../../templates/commands/hermes/fee/register-counterparty-payee_1.md CHAIN_ID=ibc-1 CHANNEL_ID=channel-0 PORT_ID=transfer COUNTERPARTY_PAYEE_ADDRESS=cosmos10h9stc5v6ntgeygf5xf945njqq5h32r53uquvw}}
```

```json
SUCCESS Successfully registered counterparty payee
```