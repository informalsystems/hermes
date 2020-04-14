# ibc-rs

> Rust implementation of IBC modules and relayer

## Disclaimer

THIS PROJECT IS UNDER HEAVY DEVELOPMENT AND IS NOT IN A WORKING STAGE NOW, USE AT YOUR OWN RISK.

## Requirements

- Rust 1.42+ (might work on earlier versions but this has not been tested yet)

## Usage

Provided that one has a Tendermint node running on port 26657, one can
configure and spawn two light clients for this chain with the following commands (to be run in the `ibc-rs` directory):

1. Fetch a trusted header from the chain:

    ```bash
    $ curl -s http://localhost:26657/status | jq '.result.sync_info|.latest_block_hash,.latest_block_height'
    ```

2. Initialize a light client for chain A with the trusted height and hash fetched in step 1:

    ```bash
    ibc-rs $ cargo run --bin relayer -- -c ./relayer/relay/tests/config/fixtures/relayer_conf_example.toml light init -x HASH -h HEIGHT chain_A
    ```
    > Replace `HASH` and `HEIGHT` with the appropriate values.

3. Repeat step 1 and 2 above for `chain_B`.

    > For this, update the height and hash, and change the chain identifier in the command above from `chain_A` to `chain_B`.

4. Start the light clients and a dummy relayer thread:

    ```bash
    ibc-rs $ cargo run --bin relayer -- -c ./relayer/relay/tests/config/fixtures/relayer_conf_example.toml start
    ```

**Note:** Add a `-v` flag to the commands above to see detailed log output, eg. `cargo run --bin relayer -- -v -c ./relayer/relay/tests/config/fixtures/relayer_conf_example.toml run`

## License

Copyright © 2020 Informal Systems

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
