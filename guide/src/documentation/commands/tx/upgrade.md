# Upgrade Tx Commands

## Table of Contents

<!-- toc -->

## Upgrade Chain

Use this to make an upgrade proposal.

```shell
USAGE:
    hermes tx upgrade-chain [OPTIONS] --reference-chain <REFERENCE_CHAIN_ID> --host-chain <HOST_CHAIN_ID> --host-client <HOST_CLIENT_ID> --amount <AMOUNT> --height-offset <HEIGHT_OFFSET>

DESCRIPTION:
    Send an IBC upgrade plan
 
OPTIONS:
        --denom <DENOM>
            Denomination for the deposit (default: 'stake')

        --new-chain <CHAIN_ID>
            New chain identifier to assign to the upgrading chain (optional)

        --new-unbonding <UNBONDING_PERIOD>
            New unbonding period to assign to the upgrading chain, in seconds (optional)

        --upgrade-name <UPGRADE_NAME>
            A string to name the upgrade proposal plan (default: 'plan')

REQUIRED:
        --amount <AMOUNT>
            Amount of stake

        --height-offset <HEIGHT_OFFSET>
            Upgrade height offset in number of blocks since current

        --reference-chain <REFERENCE_CHAIN_ID>
            Identifier of the chain to upgrade

        --host-chain <HOST_CHAIN_ID>
            Identifier of the source chain

        --host-client <HOST_CLIENT_ID>
            Identifier of the client on source chain from which the plan is created
```

__Example__

An upgrade proposal is made for `ibc-0`, for height `300` blocks from the latest height, with `10000000stake` deposited. The proposal will include the upgraded client state constructed from the state of `07-tendermint-0` client on `ibc-1`.

```shell
hermes tx upgrade-chain --reference-chain ibc-0 --host-chain ibc-1 --host-client 07-tendermint-0 --amount 10000000 --height-offset 300
```

```
Success: transaction::Hash(779713508B6103E37FADE60483BEE964A90BD67E5F20037B2CC4AE0E90B707C3)
```
