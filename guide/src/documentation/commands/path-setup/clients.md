# Client

## Table of Contents

<!-- toc -->

## Create Client

Use the `create client` command to create a new client on a destination chain,
tracking the state of the source chain.

```shell
{{#template ../../../templates/help_templates/create/client.md}}
```

__Example__

Create a new client on `ibc-0` which tracks `ibc-1`:

```shell
{{#template ../../../templates/commands/hermes/create/client_1.md HOST_CHAIN_ID=ibc-0 REFERENCE_CHAIN_ID=ibc-1}}
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
{{#template ../../../templates/help_templates/update/client.md}}
```

__Update client with latest header__

the client on `ibc-0` with the latest header of `ibc-1`:

```shell
{{#template ../../../templates/commands/hermes/update/client_1.md HOST_CHAIN_ID=ibc-0 CLIENT_ID=07-tendermint-9}}
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
{{#template ../../../templates/commands/hermes/update/client_1.md HOST_CHAIN_ID=ibc-0 CLIENT_ID=07-tendermint-1 OPTIONS=--height 320 --trusted-height 293}}
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
