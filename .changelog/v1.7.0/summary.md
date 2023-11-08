*October 20th, 2023*

This v1.7 release introduces new features and improvements to Hermes.

One of the key highlights is the addition of new misbehavior detection features.

Hermes now includes a new command called `evidence`, which monitors the blocks emitted by a chain for any presence of misbehavior evidence.

If misbehavior is detected, the CLI will report that evidence to all counterparty clients of that chain.
On top of that, misbehavior evidence detected on a chain that is a CCV (Cross-Chain Validation) consumer 
is now sent to its provider chain, alerting it directly of the misbehaving consumer chain.

Furthermore, when misbehavior is detected from an on-chain client, such as a light client attack or a double-sign,
the evidence is now submitted to all counterparty clients of the misbehaving chain, rather than just the 
counterparty client of the misbehaving client.

In addition, the REST server of Hermes now has a `/clear_packets` endpoint which allows triggering 
packet clearing for a specific chain or all chains if no specific chain is provided.

Another notable improvement is the ability to change `tracing` directives at runtime.
This feature lets users adjust tracing settings dynamically as needed, providing a more 
customizable and efficient debugging experience.

Overall, the new misbehavior detection features in Hermes contribute to a more robust and secure environment,
enabling timely identification and response to potential misbehaving actors.
