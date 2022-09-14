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

```shell
{{#template ../../../templates/commands/hermes/tx/upgrade-chain_1.md REFERENCE_CHAIN_ID=ibc-0 HOST_CHAIN_ID=ibc-1 HOST_CLIENT_ID=07-tendermint-0 AMOUNT=10000000 HEIGHT_OFFSET=300}}
```

```
Success: transaction::Hash(779713508B6103E37FADE60483BEE964A90BD67E5F20037B2CC4AE0E90B707C3)
```
