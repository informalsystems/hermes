# ibc-rs

Rust implementation of Interblockchain Communication (IBC) 
[modules](/modules) and 
[relayer](/relayer).

Includes [TLA+ specifications](/docs/spec).

## Disclaimer

THIS PROJECT IS UNDER HEAVY DEVELOPMENT AND IS NOT IN A WORKING STAGE NOW, USE AT YOUR OWN RISK.

## Releases

This project is still a pre v0.1.0 prototype. Releases can be found
[here](https://github.com/informalsystems/ibc-rs/releases)

## Installation 

Requires Rust 1.42+ (might work on earlier versions but this has not been tested yet)

These are instructions for setting up a local development environment with two
IBC-enabled local blockchains that the relayer can run against.

### Using Docker
For alternative setup using scripts, check the next section.
```shell script
docker run --rm -d -p 26656:26656 -p 26657:26657 informaldev/chain_a
docker run --rm -d -p 26556:26656 -p 26557:26657 informaldev/chain_b
```

### Using scripts
Dependencies:

- `jq`, a command-line JSON processor
- [`gaia`](https://github.com/cosmos/gaia), a blockchain supporting IBC 

Clone the relayer implementation from [iqlusioninc/relayer](https://github.com/iqlusioninc/relayer/).
We are interested in two commands we can run from this repo:

- `bash scripts/two-chainz "local" "skip"`. Running this script will instantiate two chains, listening on ports `26557` and `26657`, respectively.


- `bash dev-env`. Running this script from your local source instantiates two chains, on ports `26557` and `26657`, and starts a relayer that sets up one connection, one channel and sends a few packets over the channel.

Note that these script rely on the [cosmos/gaia](https://github.com/cosmos/gaia) implementation, which is a Cosmos-SDK application for the cosmos hub. 

## Running the Relayer

Assuming two Tendermint nodes running on local ports `26557` and `26657`.
Suppose we use the name `chain_A` to refer to the node running on port `26657`, and the name `chain_B` for the node running on port `26557`.
We can now configure and spawn two light clients for each of these chains with the following sequence of commands.
Run these from the `ibc-rs` directory:

1. Fetch a trusted header from `chain_A`:

    ```bash
    $ curl -s http://localhost:26657/status | jq '.result.sync_info|.latest_block_hash,.latest_block_height'
    ```

This should return two lines, the first one containing a hash, and the second containig the height of the chain running on `localhost:26657`.
Sample output:

```bash
"A8B490542710082377109F4B23E966F9AF924C90A4C3591E9DE9984FFABC2786"
"158"
```

2. Initialize a light client for `chain_A` with the trusted height and hash fetched in step 1:
    
    > Replace `HASH` and `HEIGHT` with the appropriate values (from step 1 above) in the following command.

    ```bash
    ibc-rs $ cargo run --bin relayer -- -c ./relayer/tests/config/fixtures/relayer_conf_example.toml light init -x HASH -h HEIGHT chain_A
    ```

3. Repeat step 1 and 2 above for `chain_B`.

    > For this, update the height and hash, and change the chain identifier in the command above from `chain_A` to `chain_B`.

4. Finally, start the main relayer thread, along with the light clients and IBC event monitor threads:

    ```bash
    ibc-rs $ cargo run --bin relayer -- -c ./relayer/tests/config/fixtures/relayer_conf_example.toml start --reset
    ```

    The `--reset` flag only needs to be passed once, for initializing the trusted headers based on the hash & height stored from steps 1-3 above.

Beside the basic relayer `start` command, the following are also available:

- `listen` will start only the monitor part of the relayer, without the light client functionality;
- `query`can be used to initiate various queries against one of the chains, for example: `cargo run --bin relayer -- -v -c ./relayer/tests/config/fixtures/relayer_conf_example.toml query connection end chain_A testconnection` will look up the connection with identifier `testconnection` on chain `chain_A`.
Note: Currently these commands fail in the response deserialization code and will be fixed as soon as  the protobuf encoding is available for tendermint and cosmos-sdk implementations.

The `relayer-cli/src/commands.rs` file contains further description of the CLI subcommands.

**Note:** Add a `-v` flag to the commands above to see detailed log output, eg. `cargo run --bin relayer -- -v -c ./relayer/tests/config/fixtures/relayer_conf_example.toml run`

## Contributing

IBC is specified in English in the [cosmos/ics repo](https://github.com/cosmos/ics). Any
protocol changes or clarifications should be contributed there.

This repo contains the TLA+ specification and Rust implementation for the IBC
modules and relayer. If you're interested in contributing, please comment on an issue or open a new
one!

## Versioning

We follow [Semantic Versioning](https://semver.org/), but none of the APIs are stable yet. Expect
anything to break with each release until `v0.1.0`.

## Resources

- [IBC Website](https://cosmos.network/ibc)
- [IBC Specification](https://github.com/cosmos/ics)
- [IBC Modules in Go](https://github.com/cosmos/cosmos-sdk/tree/master/x/ibc)
- [IBC Relayer in Go](https://github.com/iqlusioninc/relayer)

## License

Copyright © 2020 Informal Systems Inc. and ibc-rs authors.

Licensed under the Apache License, Version 2.0 (the "License"); you may not use the files in this repository except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
