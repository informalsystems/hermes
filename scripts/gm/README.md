# Gaiad Manager `gm`

## TL;DR
* Tool to manage local gaiad instances - no Docker needed.
* `scripts/gm/bin/gm install` to install it. Follow the instructions there for dependencies.
* `gm start` to start the nodes specified in the configuration.
* Config file is in `$HOME/.gm/gm.toml` play around and add more nodes.
* Tab completion is pretty good, use it! Or run `gm` by itself for help.
* Pre-1.0 warning: Got a shell error? [Raise an issue!](https://github.com/informalsystems/ibc-rs/issues/)

## Overview
Gaiad Manager (`gm` from now on) is an easily configurable command-line tool (CLI) that helps manage local `gaiad`
networks.

Typical problems running multiple `gaiad` instances involve:
* Identifying binaries and configurations for startup and nodes on the system for shutdown.
* Managing port allocations on the local machine.
* Copying and setting up configurations among nodes on the same network.
* Managing `hermes` configuration for IBC.

`gm` solves this by using a unified configuration file that describes the nodes and their relationship and automating
configuration updates.

## Requirements
* Bourne shell (`sh`)
* [`sconfig`](https://github.com/freshautomations/sconfig/releases) and
  [`stoml`](https://github.com/freshautomations/stoml/releases) installed in your PATH (put them in `/usr/local/bin`)
* `sed`, `tr` (trying to remove these in the future)
* For shell-completion Bourne Again Shell (`bash`) for the local user

## How to run
1. Install the dependencies.

On MacOS:
```bash
curl -Lo /usr/local/bin/sconfig https://github.com/freshautomations/sconfig/releases/download/v0.1.0/sconfig_darwin_amd64
curl -Lo /usr/local/bin/stoml https://github.com/freshautomations/stoml/releases/download/v0.7.0/stoml_darwin_amd64
chmod 755 /usr/local/bin/sconfig
chmod 755 /usr/local/bin/stoml
```
On Linux:
```bash
curl -Lo /usr/local/bin/sconfig https://github.com/freshautomations/sconfig/releases/download/v0.1.0/sconfig_linux_amd64
curl -Lo /usr/local/bin/stoml https://github.com/freshautomations/stoml/releases/download/v0.7.0/stoml_linux_amd64
chmod 755 /usr/local/bin/sconfig
chmod 755 /usr/local/bin/stoml
```
2. Install `gm`
```bash
git clone https://github.com/informal/ibc-rs
ibc-rs/scripts/gm/bin/gm install
```

Alternatively, you can create the folder `$HOME/.gm/bin` and copy the files from `scripts/gm/bin` in there.
The rest is just fluff.

3. Activate `gm`
* Add `source $HOME/.gm/bin/shell-support` to a file that executes when a new terminal window comes up
  (`$HOME/.bash_profile` or `$HOME/.bashrc`)
* (Optional) Enable auto-completion
On MacOS:
```bash
# Note: zsh is the default shell on MacOS, so no need to run this unless you explicitly use bash
brew install bash-completion
```
On Linux:
```
apt install bash-completion || yum install bash-completion
```
* Restart your terminal

Note: The `shell-support` script allows bash-completion as well as creating a `gm` alias, so you don't need to add more
entries to your PATH environment variable. If you don't want to use this, you can always just add `$HOME/.gm/bin` to
your path.

## Folders and files
### The HOME folder
**Where**: `$HOME/.gm`

**Description**: The hard-wired home folder for `gm` is `$HOME/.gm`. It contains the binaries required to run `gm` and
the `gm.toml` file for node configuration. By default, newly created node configuration also resides here under the
`$HOME/.gm/<node_name>` folder but that can be configured in `gm.toml`.

### The configuration: `gm.toml`
**Where**: `$HOME/.gm/gm.toml`.

**Description**: This file contains all the high-level node configuration that `gm` is aware of. Note that all entries under `[global]` are also valid entries under any `[node]` header, and can be used to override the global entries for specific nodes/validators.

**Entries**: All entries are defined and documented in the [gm.toml](gm.toml) example configuration file.

### The network configuration
**Where**: Default is the folder `$HOME/.gm/<node_name>`, but it can be configured in `gm.toml` using the `home_dir`
entry.

**Description**: The configuration and data folder for a node. Partially resembles a gaiad home folder (`.gaia`) but
it has additional files to store the wallet mnemonics.

**Entries**:
* `config` - The node configuration folder. If the node is a full-node, the genesis file was copied from a validator
config. The persistent_peers section is automatically managed if the node has the `auto_maintain_config` parameter
  enabled in `gm.toml`.
* `data` - The data folder.
* `keyring-test` - the keyring folder as defined by `gaiad testnet` with the "test" keyring-backend.
* `validator_seed.json` - the validator node's signing and wallet key.
* `wallet_seed.json` - an extra wallet mnemonic defined on validator nodes with some tokens for developer use.
* `pid` - the file that contains the process ID of the running node. (a la `/var/run`) Use `gm status` to see.
* `log` - the log file that contains the output of the running node. Use `gm log <node>` to see.

This setup allows developers to run a node outside of `gm` just by pointing the `gaiad --home-dir` to the folder.

### Ports
Ports are defined by the `ports_start_at` parameter which will be the first port assigned.
Port assignment is as follows:
```
| name            | port redirection   |
|=================|====================|
| RPC (26657)     | ports_start_at + 0 | 
| App (1317)      | ports_start_at + 1 | 
| GRPC (9090      | ports_start_at + 2 | 
| P2P (26656)     | ports_start_at + 3 | 
| PPROF (6060)    | ports_start_at + 4 | 
| GRPC-WEB (9091) | ports_start_at + 5 | 
```

Example output of `gm ports` command when `node4.ports_start_at=27050`:
```
node4 RPC  : http://localhost:27050
node4 APP  : http://localhost:27051
node4 GRPC : http://localhost:27052
node4 P2P  : http://localhost:27053
node4 PPROF: http://localhost:27054
node4 GRPCW: http://localhost:27055
```

Note: The GRPC-Web port was recently introduced (after gaiad v4.2.1). It will be ignored in earlier versions.

## Minimal configuration example
The following configuration is all you need to specify 2 `gaiad` chains. `hermes` will know about these chains.
```toml
[global]
gaiad_binary="path/to/your/gaiad"
add_to_hermes=true

[global.hermes]
binary="path/to/your/hermes"

[ibc-0]
[ibc-1]
```

This configuration specifies 2 networks (chains), `ibc-0` and `ibc-1`. A typical workflow might look like:

```bash
# Start the two chains
$ gm start

# Generate the config for `hermes`. 
# Notably, this will create the appropriate `[[chains]]` entries for `ibc-0` and `ibc-1`.
$ gm hermes config

# Generate the keys so that `hermes` can sign transactions on both chains
$ gm hermes keys

# Create a connection 
$ hermes create connection --a-chain ibc-0 --b-chain ibc-1
```

## Tribal knowledge (things they don't tell you)
* the user is welcome to create additional nodes outside the scope of `gm` on the local machine but `gm` will only
  manage nodes that are added to the configuration file.
* one quirk of the underlying tools is that if global variables are set, you can't unset them locally: empty values
  in a node configuration will revert back to the global setting.
* The shortest node definition is a named subsection like this `[mynode1]`. Ths inherently defines the following things:
  * this node is a validator
  * the chain_id of the network is `mynode1`
  * a wallet is generated with extra tokens that can be used by the developer (or by hermes)
* If you want to create a full-node, you have to define the `network="myvalidator"` option in the node configuration. If
  you do, the following things are inherently defined:
  * the node is connected to a validator called `myvalidator`
  * the `genesis.json` file is copied from that validator and the `persistent_peers` section is updated to point to the
    validator
  * if Hermes is pointed to this node in the configuration (by adding the `add_to_hermes=true` option), Hermes will get
    the wallet details from the validator node and use that wallet for transactions

## Execution manual
### `gm help`
**Description**: shows the help screen

### `gm hermes cc [--exec]`
**Description**: create and print the `hermes create channel` commands to obtain a fully interconnected IBC mesh on the screen.

`--exec` executes the commands.

Tip: Pick and choose the ones you want to create.

### `gm hermes config`
**Description**: generate the hermes `config.toml` config file and write it to the defined config path.

Tip: Do not run this command, if you value your current hermes config. It will be overwritten.

### `gm hermes keys`
**Description**: add network keys to a hermes configuration.

Tip: Make sure you set the `global.hermes_binary` entry in the config to a valid binary path.

### `gm install`
**Description**: Install the `gm` command under `$HOME/.gm`, create a default configuration and warn about missing
dependencies.

Tip: You can run this command multiple times to check if the dependencies are met.

### `gm keys [<node> ...]`
**Description**: List the keys installed on a node. (It gets them from the `keyring-test` folder.)
If no node is specified then it lists all keys.

Tip: it will show you the seed phrase if it can find it in the folder.

### `gm log <node> [<node> ...] [-f|-r]`
**Description**: Show the log of the specified node(s). At least one node has to be specified.

Tip: You can put `-f` and `-r` anywhere after `log` to get `tail -f` or `tail -r`-like functionality.

### `gm ports [<node> ...]`
**Description**: List the ports assigned to a node.
If no node is specified then it lists all nodes' ports.

Tip: When automation doesn't get you all the way, this helps in identifying your nodes on your local machine.

### `gm start [<node> ...]`
**Description**: Start the node(s). This will use the defined `gaiad` binary and configuration.
If no node is specified then it will start all nodes.

Tip: You can freely start nodes over-and-over. If they are proven running, the command will not do anything, if they
were killed for any reason, the `pid` configuration will be updated, and a fresh node started.

### `gm status`
**Description**: List all nodes and their basic properties, such as: their PID if they are running, their home folder,
and the most common ports used.

Home folders in brackets mean the configuration was not created yet. Configuration is automatically created during
startup of a node.

Tip: PIDs in brackets mean that the node is not running when `gm` started them. This could be because of a configuration
error or maybe the user simply killed the PID. No worries, `gm` will clean up when `start` or `stop` is invoked.

### `gm stop [<node> ...]`
**Description**: Stop the node(s). This will use the defined `gaiad` binary and configuration.
If no node is specified then it will stop all nodes.

Tip: If a node was killed, you can use `gm stop` to clean up the PID file.

### `gm reset [<node> ...]`
**Description**: Run `unsafe-reset-all` on the node(s) and reset the node database. This will use the defined
`gaiad` binary and configuration. If no node is specified then it will run for all nodes.

Tip: It will stop nodes that are running and restart them after the database reset.

### `gm rm <node> [<node> ...]`
**Description**: Delete the node configuration. At least one node has to be specified.

Tip: It will stop nodes that are running.

### `gm version`
**Description**: Display the version of `gm`.

Tip: Congratulations in reaching the bottom of the command references. For your endurance, you are rewarded
with an unsupported yet useful command: `gm ss` will list the open ports between 27000-28000 (the default port set
used by `gm`) on your local machine. Use it when you get port-clashes because of rogue processes on your machine that
`gm` can't account for.

## Example: 5 networks with 5 full nodes attached
This is an example that recreates the "full-mesh" tool's default network setup with the added twist that all networks
have a full node and the hermes config is going through the full nodes instead of the validator nodes.

You can get the hermes configuration automatically.

You might need to replace the value of the `gaiad_binary` entry, if you don't set `$GOPATH` in your regular executions.

The same is true for `hermes_binary`.

`gm.toml`:
```toml
[global]
gaiad_binary="$GOPATH/bin/gaiad"

[global.hermes]
binary="./hermes"

[network1]
[network2]
[network3]
[network4]
[network5]

[node1]
network="network1"
add_to_hermes=true
[node2]
network="network2"
add_to_hermes=true
[node3]
network="network3"
add_to_hermes=true
[node4]
network="network4"
add_to_hermes=true
[node5]
network="network5"
add_to_hermes=true
```
(Ports will be auto-assigned and written in the configuration file on the first start.)

Run the below:
```bash
gm start
gm hermes config
gm hermes keys
gm hermes cc 
```

This will
* create the node configuration and start all nodes
* generate the keys for hermes
* generate the config for hermes
* print the `create client` commands for a full-mesh connection among the IBC node networks.

Pick and choose the connections from the list that you want to create or run `gm hermes cc --exec` to run all the commands.
