# Tx Message Send

Test signing and sending messages via Rust

## Setup

* Clone gaia
    `git clone https://github.com/cosmos/gaia.git`
    `cd gaia`
    
* Checkout gaiav3.0 branch
    `git checkout gaiav3.0`
    
* Build 
    `make install`
    
* Configure a node

From these [instructions](https://hub.cosmos.network/master/gaia-tutorials/deploy-testnet.html)

```
gaiad init --chain-id=testing testing

gaiacli keys add validator

gaiad add-genesis-account $(gaiacli keys show validator -a) 1000000000stake,1000000000validatortoken

gaiad gentx validator

gaiad collect-gentxs

gaiad start
```

### Testing

#### Sending a transaction

Run the program and on the output copy `TxRAW` value. Open a terminal and type the copy

`curl localhost:26657/broadcast_tx_sync?tx=0x[PASTE TXRAW VALUE HERE]`

#### Decoding a messages

`echo [PASTE TXRAW VALUE HERE] | xxd -r -p | protoc --decode_raw`

**Note**: You might have to update the mnemonics with the values that you get when doing `gaiad keys add`
