# Upgrade Tx Commands

## Table of Contents

<!-- toc -->

## Upgrade Chain

Use this to make an upgrade proposal.

```shell
{{#include ../../../templates/help_templates/tx/upgrade-chain.md}}
```

__Example__

An upgrade proposal is made for `ibc-0`, for height `300` blocks from the latest height, with `10000000stake` deposited. The proposal will include the upgraded client state constructed from the state of `07-tendermint-0` client on `ibc-1`.

If the chain is using ibc-go version `v8.0.0` or higher, the authority account for the governance module needs to be used. To query the account use:

```shell
<CHAIN_BINARY> query auth module-account gov
```

or

```shell
<CHAIN_BINARY> query auth module-accounts
```

And then

```shell
{{#template ../../../templates/commands/hermes/tx/upgrade-chain_1.md REFERENCE_CHAIN_ID=ibc-0 HOST_CHAIN_ID=ibc-1 HOST_CLIENT_ID=07-tendermint-0 AMOUNT=10000000 HEIGHT_OFFSET=60 OPTIONS= --gov-account <QUERIED_ACCOUNT>}}
```

If the ibc-go version used is lower than `v8.0.0` you can ignore the `--gov-account` flag as it will not be used.

```shell
{{#template ../../../templates/commands/hermes/tx/upgrade-chain_1.md REFERENCE_CHAIN_ID=ibc-0 HOST_CHAIN_ID=ibc-1 HOST_CLIENT_ID=07-tendermint-0 AMOUNT=10000000 HEIGHT_OFFSET=60}}
```

```
Success: transaction::Hash(779713508B6103E37FADE60483BEE964A90BD67E5F20037B2CC4AE0E90B707C3)
```
