# Relaying packets

## Steps to start relaying packets between the two local chains

In order to start relaying packets please follow the steps below:

### 1. Client

#### 1.1. `create client`

First you will need to create a client for each chain:

```shell
hermes -c loop_config.toml tx raw create-client ibc-0 ibc-1
hermes -c loop_config.toml tx raw create-client ibc-1 ibc-0
```

Assuming the commands above return `07-tendermint-0` and `07-tendermint-1` respectively as the client IDs you can run the following commands to query the `client state`:

```shell
hermes -c loop_config.toml query client state ibc-0 07-tendermint-0
hermes -c loop_config.toml query client state ibc-1 07-tendermint-1
```

#### 1.2 `update client`

After you create the client, you need to execute an `update-client` transaction

```shell
hermes -c loop_config.toml tx raw update-client ibc-0 ibc-1 07-tendermint-0
hermes -c loop_config.toml tx raw update-client ibc-1 ibc-0 07-tendermint-1
```

#### 2. Connection

#### 2.1 `conn-init`

```shell
hermes -c loop_config.toml tx raw conn-init ibc-0 ibc-1 07-tendermint-0 07-tendermint-1 dummyconnection dummyconnection
```

Take note of the ID allocated by the chain, e.g. `connection-0` on `ibc-0` in order to use in the `conn-try` command below.

#### 2.2 `conn-try`

```shell
hermes -c loop_config.toml tx raw conn-try ibc-1 ibc-0 07-tendermint-1 07-tendermint-0 dummyconnection connection-0
```

Take note of the ID allocated by the chain, e.g. `connection-1` on `ibc-1`. Use in the `conn-ack` CLI

#### 2.3 conn-ack

```shell
hermes -c loop_config.toml tx raw conn-ack ibc-0 ibc-1 07-tendermint-0 07-tendermint-1 connection-0 connection-1
```

#### 2.4 conn-confirm

```shell
hermes -c loop_config.toml tx raw conn-confirm ibc-1 ibc-0 07-tendermint-1 07-tendermint-0 connection-1 connection-0
```

#### 2.5 verify that the two ends are in `Open` state

```shell
hermes -c loop_config.toml query connection end ibc-1 connection-1
```

```shell
hermes -c loop_config.toml query connection end ibc-0 connection-0
```

#### 3. Channel Open 

#### 3.1 chan-open-init

```shell
hermes -c loop_config.toml tx raw chan-open-init ibc-0 ibc-1 connection-0 transfer transfer defaultChannel defaultChannel
```

#### 3.2 chan-open-try

```shell
hermes -c loop_config.toml tx raw chan-open-try ibc-1 ibc-0 connection-1 transfer transfer defaultChannel channel-0
```

#### 3.3 chan-open-ack

```shell
hermes -c loop_config.toml tx raw chan-open-ack ibc-0 ibc-1 connection-0 transfer transfer channel-0 channel-1
```

#### 3.4 chan-open-confirm

```shell
hermes -c loop_config.toml tx raw chan-open-confirm ibc-1 ibc-0 connection-1 transfer transfer channel-1 channel-0
```

#### 3.5 verify that the two ends are in `Open` state:

```shell
hermes -c loop_config.toml query channel end ibc-0 transfer channel-0
```

```shell
hermes -c loop_config.toml query channel end ibc-1 transfer channel-1
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
    hermes -c loop_config.toml tx raw packet-send ibc-0 ibc-1 transfer channel-0 9999 1000 -n 1 -d samoleans
    ```

- query packet commitments on ibc-0

    ```shell script
    hermes -c loop_config.toml query packet commitments ibc-0 transfer channel-0
    ```

- query unreceived packets on ibc-1

    ```shell script
    hermes -c loop_config.toml query packet unreceived-packets ibc-1 ibc-0 transfer channel-0
    ```

- send recv_packet to ibc-1

    ```shell script
    hermes -c loop_config.toml tx raw packet-recv ibc-1 ibc-0 transfer channel-0
    ```

- query unreceived acks on ibc-0

    ```shell script
    hermes -c loop_config.toml query packet unreceived-acks ibc-0 ibc-1 transfer channel-1
    ```

- send acknowledgement to ibc-0

    ```shell script
    hermes -c loop_config.toml tx raw packet-ack  ibc-0 ibc-1 transfer channel-1
    ```

- send 1 packet with low timeout height offset to ibc-0

    ```shell script
    hermes -c loop_config.toml tx raw packet-send ibc-0 ibc-1 transfer channel-0 9999 2 -n 1
    ```

- send timeout to ibc-0

    ```shell script
    hermes -c loop_config.toml tx raw packet-recv ibc-1 ibc-0 transfer channel-0
    ```

Send those samoleans back, from `ibc-1` to `ibc-1`.

```shell script
hermes -c loop_config.toml tx raw packet-send ibc-1 ibc-0 transfer channel-1 9999 1000 -n 1 -d ibc/C1840BD16FCFA8F421DAA0DAAB08B9C323FC7685D0D7951DC37B3F9ECB08A199
hermes -c loop_config.toml tx raw packet-recv ibc-0 ibc-1 transfer channel-1
hermes -c loop_config.toml tx raw packet-ack  ibc-1 ibc-0 transfer channel-0
```

The `ibc/C1840BD16FCFA8F421DAA0DAAB08B9C323FC7685D0D7951DC37B3F9ECB08A199` denominator above can be obtained by querying the balance at `ibc-1` after the transfer from `ibc-0` to `ibc-1` is concluded.

#### Channel Close CLIs:

__Note__: This command is currently rejected by cosmos-sdk transfer module. To
make it work:
- clone cosmos-sdk
    ```shell script
    git clone https://github.com/cosmos/cosmos-sdk.git ~/go/src/github.com/cosmos/cosmos-sdk
    cd ~/go/src/github.com/cosmos/cosmos-sdk
    ```
- apply these diffs:
    ```
       --- a/x/ibc/applications/transfer/module.go
       +++ b/x/ibc/applications/transfer/module.go
       @@ -305,7 +305,7 @@ func (am AppModule) OnChanCloseInit(
               channelID string,
        ) error {
               // Disallow user-initiated channel closing for transfer channels
       -       return sdkerrors.Wrap(sdkerrors.ErrInvalidRequest, "user cannot close channel")
       +       return nil
        }
    ```
- append the line below (watch for the placeholder `<your>`) as the last line
  in your `go.mod` in the gaia clone:

```replace github.com/cosmos/cosmos-sdk => /Users/<your>/go/src/github.com/cosmos/cosmos-sdk```

- now `make build` and `make install` your local copy of gaia


First transfer of 5555 samoleans from `ibc-1` to `ibc-0`. This results in a
Tx to `ibc-1` for a `MsgTransfer` packet.
Make sure you're not relaying this packet (the relayer should not be running on
this path).

```shell script
hermes -c loop_config.toml tx raw packet-send ibc-1 ibc-0 transfer channel-1 5555 1000 -n 1 -d samoleans
```

Starting with channel in open-open:

- close-open

    ```shell script
    hermes -c loop_config.toml tx raw chan-close-init ibc-0 ibc-1 connection-0 transfer transfer channel-0 channel-1
    ```

- trigger timeout on close to ibc-1

    ```shell script
    hermes -c loop_config.toml tx raw packet-recv ibc-0 ibc-1 transfer channel-1
    ```

- close-close

    ```shell script
    hermes -c loop_config.toml tx raw chan-close-confirm ibc-1 ibc-0 connection-1 transfer transfer channel-1 channel-0
    ```

- verify that the two ends are in Close state:

  ```shell script
  hermes -c loop_config.toml query channel end ibc-0 transfer channel-0
  hermes -c loop_config.toml query channel end ibc-1 transfer channel-1
  ```

### Relayer loop:

Client, connection, channel handshake and packet relaying can pe done from
the relayer `v0` loop.

- start the relayer
    - with new channel:

        ```shell script
        hermes -c loop_config.toml start ibc-0 ibc-1
        ```
      The relayer should create the clients, and perform the handshake for new clients, connection and channel between the two chains on `transfer` port. Once that is finished, it listens for IBC packet events and relays receive packets, acknowledgments and timeouts.

      Note: The configuration file should have the relay path specified, for example:
      ```
        [[connections]]
        a_chain = 'ibc-0'
        b_chain = 'ibc-1'

        [[connections.paths]]
        a_port = 'transfer'
        b_port = 'transfer'
      ```

    - with existing channel:

      ```shell script
      hermes -c loop_config.toml start ibc-0 ibc-1 transfer channel-0
      ```
      The relayer listens for IBC packet events over the specified channel and relays receive packets, acknowledgments and timeouts.

- in a separate terminal, use the CLI to send 2 packets to ibc0 chain:

    ```shell script
    hermes -c loop_config.toml tx raw packet-send ibc-0 ibc-1 transfer channel-0 9999 1000 -n 2
    ```
- use the CLI to send 2 packets to ibc1 chain:

    ```shell script
    hermes -c loop_config.toml tx raw packet-send ibc-1 ibc-0 transfer channel-1 9999 1000 -n 2
    ```

- observe the output on the relayer terminal, verify that the send events are processed and the recv_packets are sent out.

- query the unreceived packets on ibc0 and ibc1 from a different terminal

    ```shell script
    hermes -c loop_config.toml query packet unreceived-packets ibc-1 ibc-0  transfer channel-0
    hermes -c loop_config.toml query packet unreceived-acks ibc-0 ibc-1 transfer channel-1
    hermes -c loop_config.toml query packet unreceived-packets ibc-0 ibc-1  transfer channel-1
    hermes -c loop_config.toml query packet unreceived-acks ibc-1 ibc-0 transfer channel-0
    ```

## Relayer listen mode

The relayer can be started in listen mode:

```shell script
hermes -c loop_config.toml listen ibc-0
```

It displays the `NewBlock` and IBC events received from the specified chain.

## Profiling the relayer

The `relayer` crate provides a `time!` macro which can be used to measure how much time is spent between the invocation of the macro and the end of the enclosing scope.

### Setup

The `time!` macro has no effect unless the `profiling` feature of the `relayer` crate is enabled.

To enable it, one must compile the `relayer-cli` crate with the `--features=profiling` flag.

a) One way is to build the `relayer` binary and update the `hermes` alias to point to the executable:

```shell script
$ cd relayer-cli/
$ cargo build --features=profiling
$ cd ..
$ alias hermes=target/debug/relayer
```

b) Alternatively, one can use the `cargo run` command and update the alias accordingly:

```shell script
$ alias hermes='cargo run --features=profiling --manifest-path=relayer-cli/Cargo.toml --'
```

The `--manifest-path=relayer-cli/Cargo.toml` flag is needed for `cargo run` to accept the `--features` flag.

### Example

```rust
fn my_function(x: u32) -> u32 {
    time!("myfunction: x={}", x); // A

    std::thread::sleep(Duration::from_secs(1));

    {
        time!("inner operation"); // B

        std::thread::sleep(Duration::from_secs(2));

        // timer B ends here
    }

    x + 1

    // timer A ends here
}
```

#### Output

```
Jan 20 11:28:46.841  INFO relayer::macros::profiling: ⏳ myfunction: x=42 - start
Jan 20 11:28:47.842  INFO relayer::macros::profiling:    ⏳ inner operation - start
Jan 20 11:28:49.846  INFO relayer::macros::profiling:    ⏳ inner operation - elapsed: 2004ms
Jan 20 11:28:49.847  INFO relayer::macros::profiling: ⏳ myfunction: x=42 - elapsed: 3005ms
```

## Parametrizing the log output level

The relayer configuration file, called `loop_config.toml` in the examples above
permits parametrization of output verbosity via the knob called `log_level`.
Relevant snippet:

```toml
[global]
timeout = '10s'
strategy = 'naive'
log_level = 'error'
```

Valid options for `log_level` are: 'error', 'warn', 'info', 'debug', 'trace'.
These levels correspond to the tracing sub-component of the relayer-cli, [see
here](https://docs.rs/tracing-core/0.1.17/tracing_core/struct.Level.html).

The relayer will _always_ print a last line summarizing the result of its
operation for queries of transactions. In addition to  this last line,
arbitrary debug, info, or other outputs may be produced.  Example, with
`log_level = 'debug'`:

```bash
Running `target/debug/relayer -c loop_config.toml query client consensus ibc-0 07-tendermint-X 0 1`
{"timestamp":"Jan 20 19:21:52.070","level":"DEBUG","fields":{"message":"registered component: abscissa_core::terminal::component::Terminal (v0.5.2)"},"target":"abscissa_core::component::registry"}
{"timestamp":"Jan 20 19:21:52.071","level":"DEBUG","fields":{"message":"registered component: relayer_cli::components::Tracing (v0.0.6)"},"target":"abscissa_core::component::registry"}
{"timestamp":"Jan 20 19:21:52.078","level":"INFO","fields":{"message":"Options QueryClientConsensusOptions { client_id: ClientId(\"07-tendermint-X\"), revision_number: 0, revision_height: 1, height: 0, proof: true }"},"target":"relayer_cli::commands::query::client"}
{"timestamp":"Jan 20 19:21:52.080","level":"DEBUG","fields":{"message":"resolving host=\"localhost\""},"target":"hyper::client::connect::dns"}
{"timestamp":"Jan 20 19:21:52.083","level":"DEBUG","fields":{"message":"connecting to [::1]:26657"},"target":"hyper::client::connect::http"}
{"timestamp":"Jan 20 19:21:52.083","level":"DEBUG","fields":{"message":"connecting to 127.0.0.1:26657"},"target":"hyper::client::connect::http"}
{"status":"error","result":["query error: RPC error to endpoint tcp://localhost:26657: error trying to connect: tcp connect error: Connection refused (os error 61) (code: 0)"]}
```

For the same command, with `log_level = 'error'`, just the last line will be
produced:

```bash
   Running `target/debug/relayer -c loop_config.toml query client consensus ibc-0 07-tendermint-X 0 1`
{"status":"error","result":["query error: RPC error to endpoint tcp://localhost:26657: error trying to connect: tcp connect error: Connection refused (os error 61) (code: 0)"]}
```

#### Next steps

Now that you have two chains running with IBC support and can execute commands on then, you can refer to the [Commands Reference](./commands.md) section to learn more about individual commands.