# Description of the parameters

This page provides a full example of a configuration file with two chains configured:

>__NOTE__: Visit the [Relaying](../commands/relaying/index.md) section to learn more about Hermes' modes.

```toml
{{#include ../../../../config.toml}}
```

For a Cosmos SDK chain that accepts ML-DSA-65 transaction signatures, set
`account_key_type = 'ml_dsa_65'` in that chain's `[[chains]]` entry. This
selects the relayer account's signing algorithm for transactions submitted to
that chain. The default is `secp256k1`. See
[Import an ML-DSA-65 relayer account](../commands/keys/index.md#import-an-ml-dsa-65-relayer-account)
for the supported key formats and import commands.
