# Upgrade Tx Commands

## Table of Contents

<!-- toc -->

## Upgrade Client

Use this to perform the upgrade for the given client.

```shell
USAGE:
    hermes tx raw upgrade-client --host-chain <HOST_CHAIN_ID> --client <CLIENT_ID>

DESCRIPTION:
    Upgrade the specified client on destination chain
    
FLAGS:
        --client <CLIENT_ID>            Identifier of the client to be upgraded
        --host-chain <HOST_CHAIN_ID>    Identifier of the chain that hosts the client
```

__Example__

A given client is upgraded:

```shell
hermes tx raw upgrade-client --host-chain ibc-1 --client 07-tendermint-0
````

```
Success: [
    UpdateClient(
        h: 1-101, cs_h: 07-tendermint-0(0-84),
    ),
    UpgradeClient(
        UpgradeClient(
            Attributes {
                height: Height {
                    revision: 1,
                    height: 101,
                },
                client_id: ClientId(
                    "07-tendermint-0",
                ),
                client_type: Tendermint,
                consensus_height: Height {
                    revision: 0,
                    height: 85,
                },
            },
        ),
    ),
]
```

## Upgrade Clients

Use this to perform the upgrade on all the clients.

```shell
USAGE:
    hermes tx raw upgrade-clients --reference-chain <REFERENCE_CHAIN_ID>

DESCRIPTION:
    Upgrade all IBC clients that target a specific chain
 
FLAGS:
        --reference-chain <REFERENCE_CHAIN_ID>
            identifier of the chain that underwent an upgrade; all clients targeting this chain will
            be upgraded
```

__Example__

All the clients are upgraded:

```shell
hermes tx raw upgrade-clients --reference-chain ibc-1
````

```
Success: [
    [
        UpdateClient(
            h: 1-111, cs_h: 07-tendermint-0(0-108),
        ),
        UpgradeClient(
            UpgradeClient(
                Attributes {
                    height: Height {
                        revision: 1,
                        height: 111,
                    },
                    client_id: ClientId(
                        "07-tendermint-0",
                    ),
                    client_type: Tendermint,
                    consensus_height: Height {
                        revision: 0,
                        height: 109,
                    },
                },
            ),
        ),
    ],
]
```

## Upgrade Chain

Use this to make an upgrade proposal.

```shell
USAGE:
    hermes tx raw upgrade-chain [OPTIONS] --dst-chain <DST_CHAIN_ID> --src-chain <SRC_CHAIN_ID> --src-client <SRC_CLIENT_ID> --amount <AMOUNT> --height-offset <HEIGHT_OFFSET>

DESCRIPTION:
    Send an IBC upgrade plan
 
FLAGS:
        --amount <AMOUNT>
            amount of stake

        --dst-chain <DST_CHAIN_ID>
            identifier of the chain to upgrade

        --height-offset <HEIGHT_OFFSET>
            upgrade height offset in number of blocks since current

        --src-chain <SRC_CHAIN_ID>
            identifier of the source chain

        --src-client <SRC_CLIENT_ID>
            identifier of the client on source chain from which the plan is created

OPTIONS:
        --denom <DENOM>
            denomination for the deposit (default: 'stake')

        --new-chain <CHAIN-ID>
            new chain identifier to assign to the upgrading chain (optional)

        --new-unbonding <PERIOD>
            new unbonding period to assign to the upgrading chain, in seconds (optional)

        --upgrade-name <NAME>
            a string to name the upgrade proposal plan (default: 'plan')

```

__Example__

An upgrade proposal is made for `ibc-0`, for height `300` blocks from latest height, with `10000000stake` deposited. The proposal will include the upgraded client state constructed from the state of `07-tendermint-0` client on `ibc-1`.

```shell
hermes tx raw upgrade-chain --dst-chain ibc-0 --src-chain ibc-1 --src-client 07-tendermint-0 --amount 10000000 --height-offset 300
```

```
Success: transaction::Hash(779713508B6103E37FADE60483BEE964A90BD67E5F20037B2CC4AE0E90B707C3)
```
