# Relayer (Rust)

This is the repository for the IBC Relayer built in Rust.

For updates please check the [releases on the ibc-rs repository](https://github.com/informalsystems/ibc-rs/releases)

## Getting Started

In order to run the Relayer please ensure you have [Rust installed on your machine](https://www.rust-lang.org/tools/install)

### Submitting an IBC transaction

There are a few `tx raw` commands that build IBC datagrams and submit them to the chains (`dest_chain_id` below).

```shell script
relayer-cli -c config.toml tx raw create-client dest_chain_id src_chain_id dest_client_id

relayer-cli -c config.toml tx raw create-client dest_chain_id src_chain_id dest_client_id

relayer-cli -c config.toml tx raw conn-init dest_chain_id src_chain_id dest_client_id src_client_id dest_connection_id -d src_connection_id

relayer-cli -c config.toml tx raw conn-try dest_chain_id src_chain_id dest_client_id src_client_id dest_connection_id src_connection_id
```
Note: This is work in progress, more commands will be implemented and tested with gaia `cosmos-test-stargate` chains.

#### Steps to testing the transactions:

* Start two chains using the `/scripts/two-chainz` script from the [cosmos/relayer](https://github.com/cosmos/relayer) (make sure to checkout the latest release, currently 0.6.1)

*  After you run the script, the Go relayer will create a `data` folder for the chains. Add the key seed file (shown below) `[GO RELAYER DATA FOLDER]/data/ibc1/key_seed.json` for chain `ibc-1` to the relayer config folder ($HOME/.rrly) using the `keys add` command below

        {    
            "name":"user",
            "type":"local",
            "address":"cosmos1tqzwwr5hrnq2ceg5fg52m720m50xpfy08at7l9",
            "pubkey":"cosmospub1addwnpepq08wntxejcla5hd93stgudw02htdpa9vu5a2ds8xkvmgrkrrpwlj6sdhkz6",
            "mnemonic":"[MNEMONIC WORDS"}
        }

    Add the key using the `keys add` command. The key file will be added exactly the above (json format and unencrypted). Later when we have a proper keyring the key file will be safely stored but for now just ensure you're using this on non-production systems.
    
    `$ cargo run --bin relayer -- -c ./relayer-cli/tests/fixtures/two_chains.toml keys add ibc-1 [GO RELAYER DATA FOLDER]/data/ibc-1/key_seed.json`
    
    After you add the key, you can check if they were properly added using the command `tree $HOME/.rrly`
    
*  Run the transaction command. In this example, it will try to initialize an `ibczeroconn2` connection on chain `ibc1`

   `$ cargo run --bin relayer -- -c ./relayer-cli/tests/fixtures/two_chains.toml tx raw conn-init ibc1 ibc0 ibczeroclient ibconeclient ibczeroconn2 -d ibconeconn`

    If you get an empty response it means the tx worked

    `conn init, result:  []`

*  Check if the connection was created on `ibc-1`:

     `$ cargo run --bin relayer -- -c ./relayer-cli/tests/fixtures/two_chains.toml query connection end ibc1 ibczeroconn2 | jq .`

    If you see an entry in the JSON file that points to the `ibczeroconn2` connection with state `STATE_INIT` it confirms that the transaction worked:


         {
               "id": "ibczeroconn2",
               "client_id": "ibczeroclient",
               "versions": [
                 "\n\u00011\u0012\rORDER_ORDERED\u0012\u000fORDER_UNORDERED"
               ],
               "state": "STATE_INIT",
               "counterparty": {
                 "client_id": "ibconeclient",
                 "connection_id": "ibconeconn",
                 "prefix": {
                   "key_prefix": "aWJj"
                 }
               }
         },
     
