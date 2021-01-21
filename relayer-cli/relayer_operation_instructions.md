
### Gaia

  1. Clone gaia:
```shell script
git clone https://github.com/cosmos/gaia.git ~/go/src/github.com/comsos/gaia
~/go/src/github.com/comsos/gaia ; git co new-main ; make install
```
  2. Start the gaia instances by running the `dev-env` script from the `ibc-rs` repo:
```shell script
./dev-env <config.toml> <chain1> <chain2>
```
e.g.:
```shell script
./dev-env my_config.toml ibc-0 ibc-1
```

### CLI Step Relaying:
You can use the relayer CLIs, below are some examples. 
Note: `alias rrly='cargo run --bin relayer --'`

#### Client CLIs:
  - create client:
```shell script
rrly -c loop_config.toml tx raw create-client ibc-0 ibc-1
rrly -c loop_config.toml tx raw create-client ibc-1 ibc-0

rrly -c loop_config.toml query client state ibc-0 07-tendermint-0
rrly -c loop_config.toml query client state ibc-1 07-tendermint-0
```

  - update client
  
```shell script
rrly -c loop_config.toml tx raw update-client ibc-0 ibc-1 07-tendermint-0
rrly -c loop_config.toml tx raw update-client ibc-1 ibc-0 07-tendermint-0
```
#### Connection CLIs:
  - init-none:

```shell script
rrly -c loop_config.toml tx raw conn-init ibc-0 ibc-1 07-tendermint-0 07-tendermint-0 dummyconnection dummyconnection
```
Take note of the ID allocated by the chain, e.g. `connection-0` on `ibc-0`. Use in the `conn-try` CLI

  - init-try:
```shell script
rrly -c loop_config.toml tx raw conn-try ibc-1 ibc-0 07-tendermint-0 07-tendermint-0 dummyconnection connection-0
```
Take note of the ID allocated by the chain, e.g. `connection-0` on `ibc-1`. Use in the `conn-ack` CLI

  - open-try:
```shell script
rrly -c loop_config.toml tx raw conn-ack ibc-0 ibc-1 07-tendermint-0 07-tendermint-0 connection-0 connection-0
```
  - open-open:
```shell script
rrly -c loop_config.toml tx raw conn-confirm ibc-1 ibc-0 07-tendermint-0 07-tendermint-0 connection-0 connection-0
```
  - verify that the two ends are in Open state:
```shell script
rrly -c loop_config.toml query connection end ibc-1 connection-0
rrly -c loop_config.toml query connection end ibc-0 connection-0
```

#### Channel CLIs:
  - init-none
```shell script
rrly -c loop_config.toml tx raw chan-init ibc-0 ibc-1 connection-0 transfer transfer defaultChannel defaultChannel
```
  - init-try
```shell script
rrly -c loop_config.toml tx raw chan-try ibc-1 ibc-0 connection-0 transfer transfer defaultChannel channel-0
```
  - open-try
```shell script
rrly -c loop_config.toml tx raw chan-ack ibc-0 ibc-1 connection-0 transfer transfer channel-0 channel-0
```
  - open-open
```shell script
rrly -c loop_config.toml tx raw chan-confirm ibc-1 ibc-0 connection-0 transfer transfer channel-0 channel-0
```
  - verify that the two ends are in Open state:
```shell script
rrly -c loop_config.toml query channel end ibc-0 transfer channel-0
rrly -c loop_config.toml query channel end ibc-1 transfer channel-0
```

#### Query balances:

  - balance at ibc-0
```shell script
gaiad --node tcp://localhost:26657 query bank balances $(gaiad --home data/ibc-0 keys --keyring-backend="test" show user -a)
```
  - balance at ibc-1
```shell script
gaiad --node tcp://localhost:26557 query bank balances $(gaiad --home data/ibc-1 keys --keyring-backend="test" show user -a)
```

Note that the addresses used in the two commands above are configured in `dev-env`.

#### Packet relaying:

First, we'll send 9999 samoleans from `ibc-0` to `ibc-1`.

  - start the transfer of 9999 samoleans from `ibc-0` to `ibc-1`. This results in a Tx to `ibc-0` for a `MsgTransfer` packet
```shell script
rrly -c loop_config.toml tx raw packet-send ibc-0 ibc-1 transfer channel-0 9999 1000 -n 1 -d samoleans
```
  - query unrecevied packets on ibc-1
```shell script
rrly -c loop_config.toml query packet unreceived-packets ibc-1 ibc-0 transfer channel-0
```
  - send recv_packet to ibc-1
```shell script
rrly -c loop_config.toml tx raw packet-recv ibc-1 ibc0 transfer transfer channel-0 channel-0
```
  - query unreceived acks on ibc-0
```shell script
rrly -c loop_config.toml query packet unreceived-acks ibc-0 ibc-1 transfer channel-0
```
  - send acknowledgement to ibc-0
```shell script
rrly -c loop_config.toml tx raw packet-ack  ibc-0 ibc-1 transfer transfer channel-0 channel-0
```
  - send 1 packet with low timeout height offset to ibc-0
```shell script
rrly -c loop_config.toml tx raw packet-send ibc-0 ibc-1 transfer channel-0 9999 2 -n 1
```
  - send timeout to ibc-0
```shell script
rrly -c loop_config.toml tx raw packet-recv ibc-0 ibc-1 transfer transfer channel-0 channel-0
```

Send those samoleans back, from `ibc-1` to `ibc-1`.

```shell script
rrly -c loop_config.toml tx raw packet-send ibc-1 ibc-0 transfer channel-0 9999 1000 -n 1 -d ibc/27A6394C3F9FF9C9DCF5DFFADF9BB5FE9A37C7E92B006199894CF1824DF9AC7C
rrly -c loop_config.toml tx raw packet-recv ibc-0 ibc-1 transfer transfer channel-0 channel-0
rrly -c loop_config.toml tx raw packet-ack  ibc-1 ibc-0 transfer transfer channel-0 channel-0
```

The `ibc/27A6394C3F9FF9C9DCF5DFFADF9BB5FE9A37C7E92B006199894CF1824DF9AC7C` denominator above can be obtained by querying the balance at `ibc-1` after the transfer from `ibc-0` to `ibc-1` is concluded.

### Relayer loop: 
Client, connection, channel handshake and packet relaying can pe done from the relayer loop

  - start the relayer, the relayer should create the clients, and do the handshake for the connection and channel. Once that is done it will sit in a loop, listening for events
```shell script
rrly -c loop_config.toml v-0
```
  - use the CLI to send 2 packets to ibc0 chain:
```shell script
rrly -c loop_config.toml tx raw packet-send ibc-0 ibc-1 transfer channel-0 9999 1000 -n 2
```
  - use the CLI to send 2 packets to ibc0 chain:
```shell script
rrly -c loop_config.toml tx raw packet-send ibc-1 ibc-2 transfer channel-0 9999 1000 -n 2
```
  - observe the output on the relayer terminal, verify that the send events are processed and the recv_packets are sent out.

  - query the unreceived packets on ibc0 and ibc1 from a different terminal
```shell script
rrly -c loop_config.toml query packet unreceived-packets ibc-1 ibc-0  transfer channel-0
rrly -c loop_config.toml query packet unreceived-acks ibc-0 ibc-1 transfer channel-0
rrly -c loop_config.toml query packet unreceived-packets ibc-0 ibc-1  transfer channel-0
rrly -c loop_config.toml query packet unreceived-acks ibc-1 ibc-0 transfer channel-0
```
