## Prerequisites

- gaiad
```
$ gaiad version --long | head -n4
name: gaia
server_name: gaiad
version: 4.0.0
commit: a279d091c6f66f8a91c87943139ebaecdd84f689
```

- Go relayer

```shell
$ rly version
version: 0.8.2
commit: 489607fa6de093d90fd2f8ac8eb52be3ccf3f145
cosmos-sdk: v0.41.3
go: go1.15.6 darwin/amd64
```

## Testing procedure

1. Patch the `one-chain` script of the Go relayer.

```shell
cd ~/go/src/github.com/cosmos/relayer/
```

This patching step is necessary to short-circuit the upgrading of a chain.
With the changes below, a chain will be able to undergo an upgrade within
~200 seconds of the upgrade proposal (instead of the default of 2 days).
With this patch, we can test the upgrade functionality in a matter of minutes.

Note this only works for MacOS ("Darwin" platform), not tests on Linux.

```diff
diff --git a/scripts/one-chain b/scripts/one-chain
index d0995fe..3702a88 100755
--- a/scripts/one-chain
+++ b/scripts/one-chain
@@ -99,6 +99,7 @@ if [ $platform = 'linux' ]; then
   sed -i 's/index_all_keys = false/index_all_keys = true/g' $CHAINDIR/$CHAINID/config/config.toml
   # sed -i '' 's#index-events = \[\]#index-events = \["message.action","send_packet.packet_src_channel","send_packet.packet_sequence"\]#g' $CHAINDIR/$CHAINID/config/app.toml
 else
+  sed -i '' 's#"172800s"#"200s"#g' $CHAINDIR/$CHAINID/config/genesis.json
   sed -i '' 's#"tcp://127.0.0.1:26657"#"tcp://0.0.0.0:'"$RPCPORT"'"#g' $CHAINDIR/$CHAINID/config/config.toml
   sed -i '' 's#"tcp://0.0.0.0:26656"#"tcp://0.0.0.0:'"$P2PPORT"'"#g' $CHAINDIR/$CHAINID/config/config.toml
   sed -i '' 's#"localhost:6060"#"localhost:'"$P2PPORT"'"#g' $CHAINDIR/$CHAINID/config/config.toml
```

2. Start two gaia instances using the patched developer environment in the Go relayer codebase:

```shell
./scripts/two-chainz
```

3. Setup the Go relayer for these chains:
```shell
$ rly tx link demo -d -o 3s
```

Check that everything went fine so far:

```shell
$ rly paths list
 0: demo                 -> chns(✔) clnts(✔) conn(✔) chan(✔) (ibc-0:transfer<>ibc-1:transfer)
```

4. Create the upgrade plan for chain ibc-0:

It's important that we parametrize the upgrade plan with a height parameter that
is at least 300 heights ahead of the current height of chain ibc-0.

First, obtain the current height:
```shell
gaiad query block | jq | grep height
      "height": "470",
```

Now create the upgrade plan for height 800:
```shell
echo '{
  "Name": "test",
  "Height": 800,
  "Info": ""
}' > ./upgrade-plan.json
```


5. Submit the upgrade plan 

```shell
rly tx upgrade-chain demo ibc-0 400h 10000000stake ./upgrade-plan.json
```

Query for the upgrade plan, check that it was submitted correctly:

```shell
$ gaiad query gov proposal 1 --home data/ibc-0/

content:
  '@type': /cosmos.upgrade.v1beta1.SoftwareUpgradeProposal
  description: upgrade the chain's software and unbonding period
  plan:
    height: "800"
    info: ""
    name: test
....
proposal_id: "1"
status: PROPOSAL_STATUS_VOTING_PERIOD
submit_time: "2021-03-08T13:07:01.417163Z"
total_deposit:
- amount: "10000000"
  denom: stake
voting_end_time: "2021-03-08T13:10:21.417163Z"
voting_start_time: "2021-03-08T13:07:01.417163Z"
```

6. Vote on the proposal

The parameter "1" should match the "proposal_id:" from the upgrade proposal
we submitted at step 5.

```shell
gaiad tx gov vote 1 yes --home data/ibc-0/data/ --keyring-backend test --keyring-dir data/ibc-0/ --chain-id ibc-0 --from validator
```

Once ibc-0 reaches height 800 (the upgrade height specified in the plan at step 4), the chain should stop executing.


7. Initialize and test Hermes

```shell
cd ~/rust/ibc-rs
```


Patch the developer env of Hermes, to redirect to the correct Gaia directory:
```diff
diff --git a/scripts/init-clients b/scripts/init-clients
index 6cf1a674..bfff9721 100755
--- a/scripts/init-clients
+++ b/scripts/init-clients
@@ -49,7 +49,7 @@ if ! grep -q -s "$CHAIN_1_ID" "$CONFIG_FILE"; then
   usage
 fi

-GAIA_DATA="$(pwd)/data"
+GAIA_DATA="~/go/src/github.com/cosmos/relayer/data"

 CHAIN_0_RPC_PORT=26657
 CHAIN_0_RPC_ADDR="localhost:$CHAIN_0_RPC_PORT"
```

No setup the clients for Hermes to use:

```shell
$ ./scripts/init-clients ~/.hermes/config.toml ibc-0 ibc-1
    Building the Rust relayer...
    Removing light client peers from configuration...
    Adding primary peers to light client configuration...
    Adding secondary peers to light client configuration...
    Importing keys...
    Done!
```

8. Test the `upgrade-client` CLI

The following command will perform the upgrade for client `07-tendermint-0`. It
will output two events, one for the updated client state, and another for the
upgraded state.

```shell
hermes tx raw upgrade-client ibc-1 ibc-0 07-tendermint-0
```
