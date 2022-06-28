# Client
The `tx raw` commands can be used to create and update the on-chain IBC clients.

## Table of Contents
<!-- toc -->

## Create Client
Use the `create-client` command to create a new client.

```shell
USAGE:
    hermes tx raw create-client [OPTIONS] --host-chain <HOST_CHAIN_ID> --reference-chain <REFERENCE_CHAIN_ID>

DESCRIPTION:
    Create a client for source chain on destination chain

FLAGS:
        --host-chain <HOST_CHAIN_ID>
            identifier of the chain that hosts the client

        --reference-chain <REFERENCE_CHAIN_ID>
            identifier of the chain targeted by the client

OPTIONS:
        --clock-drift <CLOCK_DRIFT>
            The maximum allowed clock drift for this client

        --trust-threshold <TRUST_THRESHOLD>
            Override the trust threshold specified in the configuration

        --trusting-period <TRUSTING_PERIOD>
            Override the trusting period specified in the config

```

__Example__

Create a new client of `ibc-1` on `ibc-0`:

```shell
hermes tx raw create-client --host-chain ibc-0 --reference-chain ibc-1
```

```json
{
    Success: CreateClient(
        CreateClient(
            Attributes {
                height: Height { revision: 0, height: 43 },
                client_id: ClientId(
                    "07-tendermint-0",
                ),
                client_type: Tendermint,
                consensus_height: Height { revision: 1, height: 32 },
            },
        ),
    )
}
```

A new client is created with identifier `07-tendermint-0`

## Update Client
Use the `update-client` command to update an existing client with a new consensus state.
Specific update and trusted heights can be specified.

```shell
USAGE:
    hermes tx raw update-client [OPTIONS] --host-chain <HOST_CHAIN_ID> --client <CLIENT_ID>

DESCRIPTION:
    Update the specified client on destination chain

FLAGS:
        --host-chain <HOST_CHAIN_ID>
            identifier of the chain that hosts the client

        --client <CLIENT_ID>
            identifier of the chain targeted by the client

OPTIONS:

        --height <REFERENCE_HEIGHT>
            the target height of the client update

        --trusted-height <REFERENCE_TRUSTED_HEIGHT>
            the trusted height of the client update
```

__Example__

Update the client on `ibc-0` with latest header of `ibc-1`

```shell
hermes tx raw update-client --host-chain ibc-0 --client 07-tendermint-0
```

```json
Success: UpdateClient(
    UpdateClient {
        common: Attributes {
            height: Height { revision: 0, height: 110 },
            client_id: ClientId(
                "07-tendermint-0",
            ),
            client_type: Tendermint,
            consensus_height: Height { revision: 1, height: 109 },
        },
        header: Some(
            Tendermint(
                 Header {...},
            ),
        ),
    },
)
```

The client with identifier `07-tendermint-0` has been updated with the consensus state at height `1-273`.
