# Client

## Table of Contents

<!-- toc -->

## Create Client

Use the `create client` command to create a new client on a destination chain,
tracking the state of the source chain.

```shell
USAGE:
    hermes create client [OPTIONS] --host-chain <HOST_CHAIN_ID> --reference-chain <REFERENCE_CHAIN_ID>

FLAGS:
        --host-chain <HOST_CHAIN_ID>
            identifier of the chain that hosts the client

        --reference-chain <REFERENCE_CHAIN_ID>
            identifier of the chain targeted by the client

OPTIONS:
        --clock-drift <CLOCK_DRIFT>
            The maximum allowed clock drift for this client.

            The clock drift is a correction parameter. It helps deal with clocks that are only
            approximately synchronized between the source and destination chains of this client. The
            destination chain for this client uses the clock drift parameter when deciding to accept
            or reject a new header (originating from the source chain) for this client. If this
            option is not specified, a suitable clock drift value is derived from the chain
            configurations.

        --trusting-period <TRUSTING_PERIOD>
            Override the trusting period specified in the config.

            The trusting period specifies how long a validator set is trusted for (must be shorter
            than the chain's unbonding period).

        --trust-threshold <TRUST_THRESHOLD>
            Override the trust threshold specified in the configuration.

            The trust threshold defines what fraction of the total voting power of a known and
            trusted validator set is sufficient for a commit to be accepted going forward.
```

__Example__

Create a new client on `ibc-0` which tracks `ibc-1`:

```shell
hermes create client --host-chain ibc-0 --reference-chain ibc-1
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
    hermes update client [OPTIONS] --host-chain <HOST_CHAIN_ID> --client <CLIENT_ID>

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

__Update client with latest header__

the client on `ibc-0` with latest header of `ibc-1`:

```shell
hermes update client --host-chain ibc-0 --client 07-tendermint-9
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
hermes update client --host-chain ibc-0 --client 07-tendermint-1 --height 320 --trusted-height 293
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
