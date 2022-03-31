# Start the local chains

In this chapter, you will learn how to spawn two Gaia chains, and use Hermes to relay packets between them.
To spawn the chains and configure Hermes accordingly, we will make use of script bundled in the `ibc-rs` repository.

To this end, clone the `ibc-rs` repository and check out the current version:

```bash
git clone git@github.com:informalsystems/ibc-rs.git
cd ibc-rs
git checkout v0.13.0
```

### Stop existing `gaiad` processes

If this is not the first time you are running the script, you can manually stop the two gaia instances executing the following command to kill all `gaiad` processes:

```shell
killall gaiad
```

> __NOTE__: If you have any `Docker` containers running that might be using the same ports as `gaiad` (e.g. port 26657 or port 9090), please ensure you stop them first before proceeding to the next step.

### Configuration file

In order to run the script, you will need a `TOML` configuration file to be passed as a parameter. Please check the [`Configuration`](../../config.md) section for more information about the relayer configuration file.

The following configuration file in the `ibc-rs` repository folder can be used for running the local chains:

__config.toml__

```toml
{{#include ../../../../config.toml}}
```

#### Saving the configuration file

##### Create the config.toml file

```shell
mkdir -p $HOME/.hermes && touch $HOME/.hermes/config.toml
```

##### Add content to the configuration file:

You can use your preferred text editor. If using `vi` you can run:

```shell
vi ~/.hermes/config.toml
```

Then just __`copy`__ the content for `config.toml` above and __`paste`__ into this file.

### Running the script to start the chains

From the `ibc-rs` repository folder run the following script with the parameters below to start the chains (`ibc-0` and `ibc-1`)
and import the signing keys into the keyring:

```bash
./scripts/dev-env ~/.hermes/config.toml ibc-0 ibc-1
```

> __NOTE__: If the script above prompts you to delete the data folder just answer __'yes'__

The script configures and starts two __`gaiad`__ instances, one named __`ibc-0`__ and the other __`ibc-1`__

```mermaid
graph TD
    A[dev-env] -->|run| C(start chains)
    C -->|gaiad| D[ibc-0]
    C -->|gaiad| F[ibc-1]
```

If the script runs successfully you should see a message similar to the one below in the terminal:

```shell
GAIA VERSION INFO: v4.2.1
Generating gaia configurations...
Creating gaiad instance: home=./data | chain-id=ibc-0 | p2p=:26656 | rpc=:26657 | profiling=:6060 | grpc=:9090 | samoleans=:100000000000
Change settings in config.toml file...
Start gaia on grpc port: 9090...
Balances for validator 'cosmos15cugtww7rwmayvshfznuxam55jsv23xh3jdeqv' @ 'tcp://localhost:26657'
balances:
- amount: "0"
  denom: stake
pagination:
  next_key: null
  total: "0"
Balances for user 'cosmos1usn8g2rj9q48y245pql9589zf9m8srcpxtzklg' @ 'tcp://localhost:26657'
balances:
- amount: "100000000000"
  denom: samoleans
- amount: "100000000000"
  denom: stake
pagination:
  next_key: null
  total: "0"
Creating gaiad instance: home=./data | chain-id=ibc-1 | p2p=:26556 | rpc=:26557 | profiling=:6061 | grpc=:9091 | samoleans=:100000000000
Change settings in config.toml file...
Start gaia on grpc port: 9091...
Balances for validator 'cosmos1zdmr04w7c04ef4vkuur9c0vyvl78q45qjncmja' @ 'tcp://localhost:26557'
balances:
- amount: "0"
  denom: stake
pagination:
  next_key: null
  total: "0"
Balances for user 'cosmos12p6k2dta0lsd6n80tpz34yepfpv7u7fvedm5mp' @ 'tcp://localhost:26557'
balances:
- amount: "100000000000"
  denom: samoleans
- amount: "100000000000"
  denom: stake
pagination:
  next_key: null
  total: "0"
ibc-0 initialized. Watch file /Users/ancaz/rust/ibc-rs/data/ibc-0.log to see its execution.
ibc-1 initialized. Watch file /Users/ancaz/rust/ibc-rs/data/ibc-1.log to see its execution.
Building the Rust relayer...
Importing keys...
Success: Added key 'testkey' (cosmos1usn8g2rj9q48y245pql9589zf9m8srcpxtzklg) on chain ibc-0
Success: Added key 'testkey' (cosmos12p6k2dta0lsd6n80tpz34yepfpv7u7fvedm5mp) on chain ibc-1
Done!
```

### Data directory
The script creates a __`data`__ directory in the current directory in order. The __`data`__ directory contains the chain stores and configuration files.

The __`data`__ directory has a tree structure similar to the one below:

```shell
data
├── ibc-0
│   ├── config
│   ├── data
│   ├── keyring-test
│   ├── user_seed.json
│   ├── user2_seed.json
│   └── validator_seed.json
├── ibc-0.log
├── ibc-1
│   ├── config
│   ├── data
│   ├── keyring-test
│   ├── user_seed.json
│   ├── user2_seed.json
│   └── validator_seed.json
└── ibc-1.log

```

> __Tip__: You can use the command `tree ./data/ -L 2` to view the folder structure above:

### $HOME/.hermes directory

By the default `hermes` expects the configuration file to be in the __`$HOME/.hermes`__ folder.

It also stores the private keys for each chain in this folder as outlined in the [Keys](../../commands/keys/index.md) section.

After executing the __`dev-env`__ script, this is how the folder should look like:

```shell
$HOME/.hermes/
├── config.toml
└── keys
    ├── ibc-0
    │   └── keyring-test
    │       └── testkey.json
    └── ibc-1
        └── keyring-test
            └── testkey.json
```

#### Next Steps

[The next section](./identifiers.md) describes how identifers for clients, connections and channels
are allocated, and will walk you through how to pre-allocate some identifers
to help matching them with their corresponding chains for the purpose of this tutorial.
