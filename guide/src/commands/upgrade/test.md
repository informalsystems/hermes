# Testing Client Upgrade

## Prerequisites

- gaiad `(v7.0.*)`, for example:

```shell
gaiad version --log_level error --long | head -n4
```

## Testing procedure

### Setup using Gaia manager
> Note: The `gm.toml` file that we're using here looks like this:
```
[global]
  add_to_hermes = true
  auto_maintain_config = true
  extra_wallets = 2
  gaiad_binary = "$GOPATH/bin/gaiad"
  hdpath = ""
  home_dir = "$HOME/.gm"
  ports_start_at = 27040
  validator_mnemonic = ""
  wallet_mnemonic = ""

  [global.hermes]
    binary = "<path/to/hermes>"
    config = "$HOME/.hermes/config.toml"
    log_level = "info"
    telemetry_enabled = true
    telemetry_host = "127.0.0.1"
    telemetry_port = 3001

[ibc-0]
  ports_start_at = 27000

[ibc-1]
  ports_start_at = 27010
```
* Run the command `gm start`
* Go to the file `$HOME/.gm/ibc-0/config/genesis.json` and change `max_deposit_period` and `voting_period` to a lower value, such as 200s
* Run the commands: `gm reset`, `gm hermes config` and `gm hermes keys`

### Test upgrading chain and client

1. Create one client on `ibc-1` for `ibc-0`:

    ```shell
    hermes create client --host-chain ibc-1 --reference-chain ibc-0
    ```

    ```json
    Success: CreateClient(
       CreateClient(
           Attributes {
               height: Height { revision: 1, height: 9 },
               client_id: ClientId(
                   "07-tendermint-0",
               ),
               client_type: Tendermint,
               consensus_height: Height { revision: 0, height: 18 },
           },
       ),
    )
    ```

2. Create and submit an upgrade plan for chain `ibc-0`:

    Use the hermes test command to make an upgrade proposal. In the example below a software upgrade proposal is made for `ibc-0`, for the height `300` blocks from latest height. `10000000stake` is deposited.
    The proposal includes the upgraded client state constructed from the state of `07-tendermint-0` client on `ibc-1` that was created in the previous step.

    ```shell
    hermes tx raw upgrade-chain --dst-chain ibc-0 --src-chain ibc-1 --src-client 07-tendermint-0 --amount 10000000 --height-offset 60
    ```

    ```text
    Success: transaction::Hash(CE98D8D98091BA8016BD852D18056E54C4CB3C4525E7F40DD3C40B4FD0F2482B)
    ```

    Note that the height offset should be picked such that the proposal plan height is reached after the `200s` voting period.

 3. Verify that the proposal was accepted by querying the upgrade plan to check that it was submitted correctly.

     > Note: You can find the RPC port used to query the local node by running
     > `gm ports` in order to see a list of the ports being used.

    ```shell
    gaiad --node tcp://localhost:27000 query gov proposal 1 --home $HOME/.gm/ibc-0/
    ```

    If successful, you should see output like this. Note that the status of the proposal near the bottom of the output should be
    `PROPOSAL_STATUS_VOTING_PERIOD` indicating that the voting period is still ongoing. Because we changed the `voting_period`
    parameter earlier to 200 seconds, we'll need to wait at least that long before we see the proposal take effect.

    ```text
    content:
      '@type': /ibc.core.client.v1.UpgradeProposal
      description: upgrade the chain software and unbonding period
      plan:
        height: "65"
        info: ""
        name: plan
        time: "0001-01-01T00:00:00Z"
        upgraded_client_state: null
      title: proposal 0
      upgraded_client_state:
        '@type': /ibc.lightclients.tendermint.v1.ClientState
        allow_update_after_expiry: false
        allow_update_after_misbehaviour: false
        chain_id: ibc-0
        frozen_height:
          revision_height: "0"
          revision_number: "0"
        latest_height:
          revision_height: "66"
          revision_number: "0"
        max_clock_drift: 0s
        proof_specs:
        - inner_spec:
            child_order:
            - 0
            - 1
            child_size: 33
            empty_child: null
            hash: SHA256
            max_prefix_length: 12
            min_prefix_length: 4
          leaf_spec:
            hash: SHA256
            length: VAR_PROTO
            prefix: AA==
            prehash_key: NO_HASH
            prehash_value: SHA256
          max_depth: 0
          min_depth: 0
        - inner_spec:
            child_order:
            - 0
            - 1
            child_size: 32
            empty_child: null
            hash: SHA256
            max_prefix_length: 1
            min_prefix_length: 1
          leaf_spec:
            hash: SHA256
            length: VAR_PROTO
            prefix: AA==
            prehash_key: NO_HASH
            prehash_value: SHA256
          max_depth: 0
          min_depth: 0
        trust_level:
          denominator: "0"
          numerator: "0"
        trusting_period: 0s
        unbonding_period: 1814400s
        upgrade_path:
        - upgrade
        - upgradedIBCState
    deposit_end_time: "2022-07-06T15:14:38.993051Z"
    final_tally_result:
      abstain: "0"
      "no": "0"
      no_with_veto: "0"
      "yes": "0"
    proposal_id: "1"
    status: PROPOSAL_STATUS_VOTING_PERIOD
    submit_time: "2022-07-06T15:12:38.993051Z"
    total_deposit:
    - amount: "10000000"
      denom: stake
    voting_end_time: "2022-07-06T15:14:38.993051Z"
    voting_start_time: "2022-07-06T15:12:38.993051Z"
    ```

 4. Vote on the proposal

    The parameter `1` should match the `proposal_id:` from the upgrade proposal submitted at step 3.
    This command must be issued while the proposal status is `PROPOSAL_STATUS_VOTING_PERIOD`. Confirm transaction when prompted.

    ```shell
    gaiad --node tcp://localhost:27000 tx gov vote 1 yes --home $HOME/.gm/ibc-0/data/ --keyring-backend test --keyring-dir $HOME/.gm/ibc-0/ --chain-id ibc-0 --from validator
    ```

    ```text
    confirm transaction before signing and broadcasting [y/N]: y

    {"height":"85","txhash":"AC24D80B1BFE0832769DECFDD3B3DF999A363D5E4390B0B673344FFDED9150B2","codespace":"","code":0,"data":"0A060A04766F7465","raw_log":"[{\"events\":[{\"type\":\"message\",\"attributes\":[{\"key\":\"action\",\"value\":\"vote\"},{\"key\":\"module\",\"value\":\"governance\"},{\"key\":\"sender\",\"value\":\"cosmos1srfzw0jkyyn7wf0ps4zy0tuvdaclfj2ufgp6w3\"}]},{\"type\":\"proposal_vote\",\"attributes\":[{\"key\":\"option\",\"value\":\"VOTE_OPTION_YES\"},{\"key\":\"proposal_id\",\"value\":\"1\"}]}]}]","logs":[{"msg_index":0,"log":"","events":[{"type":"message","attributes":[{"key":"action","value":"vote"},{"key":"module","value":"governance"},{"key":"sender","value":"cosmos1srfzw0jkyyn7wf0ps4zy0tuvdaclfj2ufgp6w3"}]},{"type":"proposal_vote","attributes":[{"key":"option","value":"VOTE_OPTION_YES"},{"key":"proposal_id","value":"1"}]}]}],"info":"","gas_wanted":"200000","gas_used":"43716","tx":null,"timestamp":""}
    ```

  5. Wait approximately 200 seconds until the proposal changes status to `PROPOSAL_STATUS_PASSED`.
     Note the `final tally_result` that includes the vote submitted in the previous step.

      ```shell
      gaiad --node tcp://localhost:27000 query gov proposal 1 --home $HOME/.gm/ibc-0/
      ```

     ```text
        content:
          '@type': /cosmos.upgrade.v1beta1.SoftwareUpgradeProposal
          description: upgrade the chain software and unbonding period
        ...
        final_tally_result:
          abstain: "0"
          "no": "0"
          no_with_veto: "0"
          "yes": "100000000000"
        proposal_id: "1"
        status: PROPOSAL_STATUS_PASSED
        submit_time: "2021-04-12T16:30:17.187389Z"
        total_deposit:
        - amount: "10000000"
          denom: stake
        voting_end_time: "2021-04-12T16:33:37.187389Z"
        voting_start_time: "2021-04-12T16:30:17.187389Z"
     ```

6. Test the `upgrade client` CLI

    The following command performs the upgrade for client `07-tendermint-0`. It outputs two events, one for the updated client state,
    and another for the upgraded state.  
    The `--upgrade-height 65` value is taken from the `height` in the upgrade plan output.

    ```shell
    hermes upgrade client --host-chain ibc-1 --client 07-tendermint-0 --upgrade-height 65
    ```
    ```json
    Success: [
        UpdateClient(
            UpdateClient {
                common: Attributes {
                    height: Height { revision: 1, height: 438 },
                    client_id: ClientId(
                        "07-tendermint-0",
                    ),
                    client_type: Tendermint,
                    consensus_height: Height { revision: 0, height: 440 },
                },
                header: Some(
                    Tendermint(..)
                ),
            },
        ),
        UpgradeClient(
            UpgradeClient(
                Attributes {
                    height: Height { revision: 1, height: 438 },
                    client_id: ClientId(
                        "07-tendermint-0",
                    ),
                    client_type: Tendermint,
                    consensus_height: Height { revision: 0, height: 441 },
                },
            ),
        ),
    ]
    ```

If the command fails with the error:

```shell
Error: failed while trying to upgrade client id 07-tendermint-0 for chain ibc-0: failed while fetching from chain the upgraded client state: conversion from a protobuf `Any` into a domain type failed: conversion from a protobuf `Any` into a domain type failed: error converting message type into domain type: the client state was not found
```

It might be due to the chain not being at the height defined for the upgrade. This can be checked with the INFO output of the command:

```shell
INFO ThreadId(01) [ibc-0 -> ibc-1:07-tendermint-0] upgrade Height: 0-82
```

Where in this case the chain is at height 82.
