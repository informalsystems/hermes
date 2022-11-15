# Misbehaviour

## Table of Contents
<!-- toc -->

## Monitoring Misbehaviour and Evidence Submission
Use the `misbehaviour` command to monitor the updates for a given client, detect certain types of misbehaviour and
submit evidence to the chain. If the evidence passes the on-chain validation, the client is frozen. Further packets
cannot be relayed using the frozen client.

```shell
{{#include ../../../templates/help_templates/misbehaviour.md}}
```

The misbehaviour monitor starts by analyzing all headers used in prior client updates.
Once finished it registers for update client events and checks any new headers for misbehaviour.
If it detects evidence of misbehaviour, it submits a transaction with the evidence to the chain.
If the chain validates the transaction then the monitor exits.

> This is an experimental feature.

The following types of misbehaviour are handled:
1. **Fork**

    Assumes at least one consensus state before the fork point exists.
    Let existing consensus states on chain B be: `[Sn,.., Sf, Sf-1, S0]` with `Sf-1` being
    the most recent state before the fork.
    Chain A is queried for a header `Hf'` at `Sf.height` and if it is different from the `Hf`
    in the event for the client update (the one that has generated `Sf` on chain), then the two
    headers are included in the evidence and submitted.
    Note that in this case the headers are different but have the same height.

2. **BFT time violation for an unavailable header**

    Some header with a height that is higher than the latest
    height on chain `A` has been accepted and, a consensus state was created on `B`. Note that this implies
    that the timestamp of this header must be within the `clock_drift` of the client.
    Assume the client on `B` has been updated with `h2`(not present on/ produced by chain `A`)
    and it has a timestamp of `t2` that is at most `clock_drift` in the future.
    Then the latest header from `A` is fetched, let it be `h1`, with a timestamp of `t1`.
    If `t1 >= t2` then evidence of misbehavior is submitted to A.

__Example__

The `misbehaviour` command outputs an error message displaying `MISBEHAVIOUR DETECTED`:

```shell
{{#template ../../../templates/commands/hermes/misbehaviour_1.md CHAIN_ID=ibc-0 CLIENT_ID=07-tendermint-0}}
```

```json
Apr 13 20:04:03.347  INFO ibc_relayer::foreign_client: checking misbehaviour for consensus state heights [Height { revision: 1, height: 195 }, Height { revision: 1, height: 85 }, Height { revision: 1, height: 28 }]
Apr 13 20:04:04.425 ERROR ibc_relayer::foreign_client: MISBEHAVIOUR DETECTED ClientId("07-tendermint-0") h1: Height { revision: 1, height: 195 }-Height { revision: 1, height: 85 } h2: Height { revision: 1, height: 195 }-Height { revision: 1, height: 85 }, sending evidence
Apr 13 20:04:05.070  INFO ibc_relayer_cli::commands::misbehaviour: evidence submission result [ClientMisbehaviour(ClientMisbehaviour(Attributes { height: Height { revision: 0, height: 1521 }, client_id: ClientId("07-tendermint-0"), client_type: Tendermint, consensus_height: Height { revision: 1, height: 195 } }))]

Success: Some(
    ClientMisbehaviour(
        ClientMisbehaviour(
            Attributes {
                height: Height {
                    revision: 0,
                    height: 1521,
                },
                client_id: ClientId(
                    "07-tendermint-0",
                ),
                client_type: Tendermint,
                consensus_height: Height {
                    revision: 1,
                    height: 195,
                },
            },
        ),
    ),
)
```

Querying client state from this point will show the client is in frozen state, with `frozen_height` indicating the height at which the client was frozen:
```shell
{{#template ../../../templates/commands/hermes/query/client/state_1.md CHAIN_ID=ibc-0 CLIENT_ID=07-tendermint-0}} | jq
```
Which should output:
```json
{
  "result": {
    "allow_update_after_expiry": true,
    "allow_update_after_misbehaviour": true,
    "chain_id": "ibc-1",
    "frozen_height": {
      "revision_height": 16,
      "revision_number": 1
    },
    "latest_height": {
      "revision_height": 16,
      "revision_number": 1
    },
    "max_clock_drift": {
      "nanos": 0,
      "secs": 3
    },
    "trust_threshold": {
      "denominator": "3",
      "numerator": "1"
    },
    "trusting_period": {
      "nanos": 0,
      "secs": 1209600
    },
    "unbonding_period": {
      "nanos": 0,
      "secs": 1814400
    },
    "upgrade_path": [
      "upgrade",
      "upgradedIBCState"
    ]
  },
  "status": "success"
}
```
