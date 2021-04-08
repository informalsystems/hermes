## Prerequisites

- gaiad `(v4.1.*)`, for example:

```shell
$ gaiad version --long | head -n4
name: gaia
server_name: gaiad
version: 4.1.2
commit: 95b07e641d1f69ee12dd911e92b1679f2c64d385
```

## Testing procedure

1. Start two gaia instances and initialize hermes:

    ```shell
    $ ./scripts/dev-env ~/.hermes/config.toml ibc-0 ibc-1
    ```
    The `one-chain` script is invoked for each chain and modifies the `genesis.json` file to use a short window for governance proposals (`200s` for `max_deposit_period` and `voting_period`). Therefore, an upgrade proposal can be submitted, voted on and accepted within a short time.

2. Create one client on `ibc-1` for `ibc-0`:

    ```shell
    $ hermes create client ibc-1 ibc-0
    ```

3. Create and submit an upgrade plan for chain `ibc-0`:

    Use the hermes test command to make an upgrade proposal. In the example below a software upgrade proposal is made for `ibc-0`, for the height `300` blocks from latest height. `10000000stake` is deposited.
    The proposal includes the upgraded client state constructed from the state of `07-tendermint-0` client on `ibc-1` that was created in the previous step. In addition, the `unbonding_period` of the client is set to some new value (`400h`)

    ```shell
    $ hermes tx raw upgrade-chain ibc-0 ibc-1 07-tendermint-0 10000000 300
    ```

    Note that the height offset should be picked such that the proposal plan height is reached after the `200s` voting period.

 4. Verify that the proposal was accepted:

    Query the upgrade plan to check that it was submitted correctly. Note the `height` at which the proposal will take effect (chain halts). Also `status: PROPOSAL_STATUS_VOTING_PERIOD`.

    ```shell
    $ gaiad query gov proposal 1 --home data/ibc-0/

    content:
      '@type': /cosmos.upgrade.v1beta1.SoftwareUpgradeProposal
      description: upgrade the chain software and unbonding period
      plan:
        height: "382"
        info: upgrade the chain software and unbonding period
        name: test
        time: "0001-01-01T00:00:00Z"
        upgraded_client_state:
          '@type': /ibc.lightclients.tendermint.v1.ClientState
          allow_update_after_expiry: false
          allow_update_after_misbehaviour: false
          chain_id: ibc-0
          frozen_height:
            revision_height: "0"
            revision_number: "0"
          latest_height:
            revision_height: "383"
            revision_number: "0"
          max_clock_drift: 0s
          proof_specs:
    ...
          trust_level:
            denominator: "0"
            numerator: "0"
          trusting_period: 0s
          unbonding_period: 1440000s
          upgrade_path:
          - upgrade
          - upgradedIBCState
      title: upgrade_ibc_clients
    deposit_end_time: "2021-03-23T17:25:42.543572Z"
    final_tally_result:
      abstain: "0"
      "no": "0"
      no_with_veto: "0"
      "yes": "0"
    proposal_id: "1"
    status: PROPOSAL_STATUS_VOTING_PERIOD
    submit_time: "2021-03-23T17:22:22.543572Z"
    total_deposit:
    - amount: "10000000"
      denom: stake
    voting_end_time: "2021-03-23T17:25:42.543572Z"
    voting_start_time: "2021-03-23T17:22:22.543572Z"
    ```

 5. Vote on the proposal

    The parameter `1` should match the `proposal_id:` from the upgrade proposal submitted at step 3. This command must be issued while the proposal status is `PROPOSAL_STATUS_VOTING_PERIOD`.

    ```shell
    gaiad tx gov vote 1 yes --home data/ibc-0/data/ --keyring-backend test --keyring-dir data/ibc-0/ --chain-id ibc-0 --from validator
    ```

    Wait approximately 200 seconds until the proposal changes status to `PROPOSAL_STATUS_PASSED`. Note the `final tally_result` that includes the vote submitted in previous step.

    ```shell
    $ gaiad query gov proposal 1 --home data/ibc-0/

    content:
      '@type': /cosmos.upgrade.v1beta1.SoftwareUpgradeProposal
      description: upgrade the chain software and unbonding period
      plan:
    ...
    final_tally_result:
      abstain: "0"
      "no": "0"
      no_with_veto: "0"
      "yes": "100000000000"
    proposal_id: "1"
    status: PROPOSAL_STATUS_PASSED
    submit_time: "2021-03-23T17:22:22.543572Z"
    total_deposit:
    - amount: "10000000"
      denom: stake
    voting_end_time: "2021-03-23T17:25:42.543572Z"
    voting_start_time: "2021-03-23T17:22:22.543572Z"
    ```

6. Test the `upgrade-client` CLI

    The following command performs the upgrade for client `07-tendermint-0`. It outputs two events, one for the updated client state, and another for the upgraded state.

    ```shell
    $ hermes tx raw upgrade-client ibc-1 ibc-0 07-tendermint-0

    {
      "status": "success",
      "result": [
        {
          "UpdateClient": {
            "client_id": "07-tendermint-0",
            "client_type": "Tendermint",
            "consensus_height": {
              "revision_height": 332,
              "revision_number": 0
            },
            "height": {
              "revision_height": 404,
              "revision_number": 1
            }
          }
        },
        {
          "UpgradeClient": {
            "client_id": "07-tendermint-0",
            "client_type": "Tendermint",
            "consensus_height": {
              "revision_height": 333,
              "revision_number": 0
            },
            "height": {
              "revision_height": 404,
              "revision_number": 1
            }
          }
        }
      ]
    }
    ```
