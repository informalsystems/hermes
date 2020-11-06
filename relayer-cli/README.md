# Relayer (Rust)

This is the repository for the IBC Relayer built in Rust.

For updates please check the [releases on the ibc-rs repository](https://github.com/informalsystems/ibc-rs/releases)

## Getting Started

In order to run the Relayer please ensure you have [Rust installed on your machine](https://www.rust-lang.org/tools/install)

### Submitting an IBC transaction

The `tx raw conn-init` command works now. Signing the message is working and the gaia chain (stargate-4) accepts the transaction. 

#### Steps to testing the transaction: 

* Start two chains using the `dev-env` script from the [ovrclk/relayer](https://github.com/ovrclk/relayer) (make sure to checkout stargate-4 version)
*  After you run the script, the Go relayer will create a `data` folder for the chains. Open the key seed file `./data/ibc1/key_seed.json` for chain `ibc-1` and look for the account value


        {    
            "name":"user",
            "type":"local",
            "address":"cosmos1tqzwwr5hrnq2ceg5fg52m720m50xpfy08at7l9",
            "pubkey":"cosmospub1addwnpepq08wntxejcla5hd93stgudw02htdpa9vu5a2ds8xkvmgrkrrpwlj6sdhkz6",
            "mnemonic":"[MNEMONIC WORDS"}
        }

*  Run command to add the key to the configured chain

    `[TODO]`

*  Run the transaction command. This will try to initialize an `ibczeroconn2` connection on chain `ibc1`

   `$ cargo run --bin relayer -- -c ./relayer-cli/tests/fixtures/two_chains.toml tx raw conn-init ibc0 ibc1 ibczeroclient ibconeclient ibczeroconn2 ibconeconn`

    If you get an empty response it means the tx worked

    `conn init, result:  []`

*  Check if the connection was created on `ibc-1` using the Golang relayer

     `$ rly query connections ibc1 | jq .`

    If you see an entry in the JSON file that points to the `ibczeroconn2` connection with state `STATE_INIT` it confirms that the transaction worked:


         {
               "id": "ibczeroconn21",
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
     





