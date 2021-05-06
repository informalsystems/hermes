# Multi-chain (full-mesh) tool
This tool will create multiple chains and IBC connections among them with minimal help.

Tested on MacOS Mojave.

## Requirements
* Docker
* `make` for convenient command execution

Note: the files are kept simple where possible. If `make` is not available, you can copy-paste the instructions from the
Makefile fairly easily.

## Quick start
Run the below to create 5 blockchain networks with a full mesh of IBC connections.
```
make
```
The chains will be named network1, network2, network3, network4 and network5 and they are created using `docker compose`.

Sending all IBC connection messages can take up to 10-12 minutes (todo: make this parallel).

If you want something quicker, run the same command instead for 3 blockchain networks by running:
```
make N=3
```

All configuration is locally editable: networks have their own folder with the configuration and the database so
you can easily change anything or reset the network. Networks can be stopped and restarted using regular docker commands.

The hermes configuration is stored locally under the `.hermes` folder.

To delete all networks and configuration, run:
```
make clean
```
This will stop the chains, the relayers and clean up the configuration files.

### Less-than full mesh
You can tell the setup process which blockchain networks should have IBC connections.

For this, you have to run the setup process in two steps and edit a file in-between that describes the network connections:
```
make setup-network
vi paths
make setup-relay
```
The first step will run the blockchain networks and provide a file (`paths`) that contains the full-mesh configuration.
Edit this file to your liking by removing any connections among blockchain networks that you don't want to set up.
The third command will resume the setup process and create the hermes configuration and start the relayers based on this file.

Example paths file for a five-network full mesh:
```
# IBC full-mesh connection graph
1 2
1 3
1 4
1 5
2 3
2 4
2 5
3 4
3 5
4 5
```

## Command reference

![MAKE command hierarchy](make.png "MAKE hierarchy")

### `make all`
* Same as `make`.
* Equals to `make setup-network setup-relay`
* Creates a 5-network full-mesh. Use the `N=` parameter to change the number of networks.

### `make setup-network`
* Set up the configuration for the gaiad blockchain networks and start them using docker compose.
* Equals to `make config-files network-up`
* Creates a 5-network full-mesh. Use the `N=` parameter to change the number of networks.

### `make setup-relay`
* Set up the configuration for hermes and the relayer processes and start them using docker compose.
* Equals to `make config-onchain relay-up`
* Uses the `paths` file to figure out which networks have connections.

### `make config-files`
* Creates the blockchain networks configuration files. (Under `network1`, `network2`, etc...)
* Creates the `.hermes` folder and adds all network keys to hermes.
* Creates the `paths` file with the descriptions of the network connections.
* Equals to running two bash scripts (`1-create-network-config.sh` and `2-create-hermes-config.sh`).
* Creates a 5-network configuration. Use the `N=` parameter to change the number of networks.

### `make network-up`
* Runs the gaiad blockchain networks using docker.
* Equals to `docker compose -f docker-compose.gaiad.yml -p gaiad up -d`
* Pairs with `make network-down`.

Convenience function. There is another set of containers (the relayers) that are configured separately with less parameters.
(Hence the `--project` and `--file` parameters here.)

### `make config-onchain`
* Configure the networks' IBC connections to each other using hermes.
* Configure the `docker-compose.yml` that describes the relayer processes among the networks.
* Equals to running two bash scripts (`3-create-onchain-config.sh` and `4-create-relayer-config.sh`).
* Uses the `paths` file to figure out which networks connect to which networks.

### `make relay-up`
* Start the hermes relayer services using `docker-compose.yml`.
* Equals to `docker compose up -d` (yay, easy).
* Pairs with `make relay-down`.

### `make relay-down`
* Stop the hermes relayer services using `docker-compose.yml`.
* This does not delete the hermes configuration.
* Equals to `docker compose down`.
* Pairs with `make relay-up`.

### `make network-down`
* Stop and delete the gaiad blockchain networks' docker containers.
* This does not delete the blockchain configuration or database.
* Equals to `docker compose -f docker-compose.gaiad.yml -p gaiad down -d`
* Pairs with `make network-up`.

### `make network-start`
* Start an existing gaiad blockchain networks' docker containers that were previously stopped.
* Equals to `docker compose -f docker-compose.gaiad.yml -p gaiad start`
* Pairs with `make network-stop`.

### `make network-stop`
* Stop a running set of gaiad blockchain networks' docker containers.
* Equals to `docker compose -f docker-compose.gaiad.yml -p gaiad stop`
* Pairs with `make network-start`.

### `make clean`
* Stop and delete all docker containers (gaiad and relayers).
* Delete all networks data and configuration as well as hermes configuration.
* Might show error messages on the screen if some of the docker containers are not running.
  It will still exit with error code 0.

## Wallets
Each chain has two wallet addresses preconfigured with tokens: one for the validator and one additional for generic use.

Wallets can be reached by using the `--keyring-backend test --keyring-dir networkX` parameters where networkX is the
chain's configuration folder.

## Ports
All ports are forwarded to the host machine on port 26XXY where XX is the (zero-padded) network identifier number and
Y is the port as follows:
```
0 - RPC (26657)
1 - APP (1317)
2 - GRPC (9090)
3 - P2P (26656)
```

This way `network1`'s ports are:
```
26010 - RPC
26011 - APP
26012 - GRPC
26013 - P2P
```

whereas `network5`'s ports are:
```
26050 - RPC
26051 - APP
26052 - GRPC
26053 - P2P
```

## Examples
Query list of keys on network1:
```
gaiad keys list --keyring-backend test --keyring-dir network1
```

Get the account balance of a key on network1:
```
gaiad query bank balances cosmos135vqr04clpx0d0nw3xljpuggps7ffvq3u5mww7 --node http://localhost:26010
```

## Statistics
Setup on my machine:
* N=2 takes about 1.5 minutes
* N=3 takes about 4 minutes
* N=4 takes about 8 minutes
* N=5 takes about 11 minutes
