# Relayer (Rust)

This is the repository for the IBC Relayer built in Rust.

For updates please check the [releases on the ibc-rs repository](https://github.com/informalsystems/ibc-rs/releases)

## Getting Started

In order to run the Relayer please ensure you have [Rust installed on your machine](https://www.rust-lang.org/tools/install)

### Submitting an IBC transaction

There are a few `tx raw` commands that build IBC datagrams and submit them to the chains (`dest_chain_id` below).

```shell script
relayer-cli -c config.toml tx raw create-client dest_chain_id src_chain_id dest_client_id -k seed_file.json

relayer-cli -c config.toml tx raw create-client dest_chain_id src_chain_id dest_client_id -k seed_file.json

relayer-cli -c config.toml tx raw conn-init dest_chain_id src_chain_id dest_client_id src_client_id dest_connection_id -d src_connection_id
    -k seed_file.json
```

Note: This is work in progress, more commands will be implemented and tested with gaia stargate-4 chains.
As shown above the tx commands currently require specifying a seed file:

* **seed_file** (-k) -> specify a key file (name and location) that will be used by the signer. This key seed file must include a mnemonic (seed phrase) that can be used to retrieve the private key (BIP-39) used to sign the transaction.

#### Steps to testing the transactions:

* Start two chains using the `dev-env` script from the [ovrclk/relayer](https://github.com/ovrclk/relayer) (make sure to checkout stargate-4 version)
*  After you run the script, the Go relayer will create a `data` folder for the chains. Open the key seed file `./data/ibc1/key_seed.json` for chain `ibc-1` and look for the account value


        {    
            "name":"user",
            "type":"local",
            "address":"cosmos1tqzwwr5hrnq2ceg5fg52m720m50xpfy08at7l9",
            "pubkey":"cosmospub1addwnpepq08wntxejcla5hd93stgudw02htdpa9vu5a2ds8xkvmgrkrrpwlj6sdhkz6",
            "mnemonic":"[MNEMONIC WORDS"}
        }

*  Run the transaction command. In this example, it will try to initialize an `ibczeroconn2` connection on chain `ibc1`

   `$ cargo run --bin relayer -- -c ./relayer-cli/tests/fixtures/two_chains.toml tx raw conn-init ibc1 ibc0 ibczeroclient ibconeclient ibczeroconn2 -d ibconeconn -k key_seed.json`

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
     