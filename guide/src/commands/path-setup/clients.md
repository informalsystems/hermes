# Client

## Table of Contents

<!-- toc -->

## Create Client

Use the `create client` command to create a new client.

```shell
USAGE:
    hermes create client <OPTIONS>

DESCRIPTION:
    Create a new IBC client

POSITIONAL ARGUMENTS:
    dst_chain_id              identifier of the destination chain
    src_chain_id              identifier of the source chain
```

__Example__

Create a new client of `ibc-1` on `ibc-0`:

```shell
hermes create client ibc-0 ibc-1
```

```json
    CreateClient(
        Attributes {
            height: Height {
                revision: 0,
                height: 286,
            },
            client_id: ClientId(
                "07-tendermint-0",
            ),
            client_type: Tendermint,
            consensus_height: Height {
                revision: 1,
                height: 274,
            },
        },
    ),
)
```

A new client is created with identifier `07-tendermint-1`

## Update Client

Use the `update client` command to update an existing client with a new consensus state.
Specific update and trusted heights can be specified.

```shell
USAGE:
    hermes update client <OPTIONS>

DESCRIPTION:
    Update an IBC client

POSITIONAL ARGUMENTS:
    dst_chain_id              identifier of the destination chain
    dst_client_id             identifier of the client to be updated on destination chain

FLAGS:
    -h, --target-height TARGET-HEIGHT
    -t, --trusted-height TRUSTED-HEIGHT
```

__Update client with latest header__

the client on `ibc-0` with latest header of `ibc-1`:

```shell
hermes update client ibc-0 07-tendermint-9
```

```json
Success: UpdateClient(
    UpdateClient {
        common: Attributes {
            height: Height { revision: 0, height: 303 },
            client_id: ClientId(
                "07-tendermint-1",
            ),
            client_type: Tendermint,
            consensus_height: Height { revision: 1, height: 293 },
        },
        header: Some(
            Tendermint(
                 Header {...},
            ),
        ),
    },
)
```

The client with identifier `07-tendermint-1` has been updated with the consensus state at height `1-293`.

__Update a client to a specific target height__

```shell
hermes update client ibc-0 07-tendermint-1 --target-height 320 --trusted-height 293
```

```json
Success: UpdateClient(
    UpdateClient {
        common: Attributes {
            height: Height { revision: 0, height: 555 },
            client_id: ClientId(
                "07-tendermint-1",
            ),
            client_type: Tendermint,
            consensus_height: Height { revision: 1, height: 320 },
        },
        header: Some(
            Tendermint(
                 Header {...},
            ),
        ),
    },
)
```

The client with identifier `07-tendermint-1` has been updated with the consensus state at height `1-320`, as specified.
