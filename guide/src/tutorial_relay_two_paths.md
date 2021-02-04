# Bidirectional Relaying

At the moment, one Hermes instance relays packets over a single channel.
To relay packets over multiple channels, one needs to spawn multiple instances.

> Due to a current limitation, an instance needs its own configuration file
and its own `data` folder. The steps below describe the process for setting things
up properly for two hermes instances.

1. From the `ibc-rs` repository folder run the following script with the parameters below to start the chains (`ibc-0` and `ibc-1`):

    ```bash
    ./scripts/setup-chains ibc-0 ibc-1
    ```

    > __NOTE__: If the script above prompts you to delete the data folder just answer __'yes'__

    The script configures and starts two __`gaiad`__ instances, one named __`ibc-0`__ and the other __`ibc-1`__

2. From the root of the working copy of `ibc-rs`, create a folder for the first instance:

    ```shell
    $ mkdir relay_a && cd relay_a
    ```

3. Paste the following configuration in a file named `config.toml` in the `relay_a` directory:

    ```toml
    [global]
    timeout = '10s'
    strategy = 'naive'
    log_level = 'error'

    [[chains]]
    id = 'ibc-0'
    rpc_addr = 'tcp://localhost:26657'
    grpc_addr = 'tcp://localhost:9090'
    account_prefix = 'cosmos'
    key_name = 'testkey'
    store_prefix = 'ibc'
    gas = 200000
    clock_drift = '5s'
    trusting_period = '14days'

    [chains.trust_threshold]
    numerator = '1'
    denominator = '3'

    [[chains]]
    id = 'ibc-1'
    rpc_addr = 'tcp://localhost:26557'
    grpc_addr = 'tcp://localhost:9091'
    account_prefix = 'cosmos'
    key_name = 'testkey'
    store_prefix = 'ibc'
    gas = 200000
    clock_drift = '5s'
    trusting_period = '14days'

    [chains.trust_threshold]
    numerator = '1'
    denominator = '3'

    [[connections]]
    a_chain = "ibc-1"
    b_chain = "ibc-0"

    [[connections.paths]]
    a_port = 'transfer'
    b_port = 'transfer'
    ```

4. Create the data folders for both chains:

    ```shell
    $ mkdir -p data/ibc-0/data
    $ mkdir -p data/ibc-1/data
    ```

5. Copy the keys over from the chains `data` directory:

    ```shell
    $ cp ../data/ibc-0/key_seed.json data/ibc-0/
    $ cp ../data/ibc-1/key_seed.json data/ibc-1/
    ```
6. Initialize the light clients:

    ```shell
    $ ../scripts/init-clients config.toml ibc-0 ibc-1
    ```

7. Let's proceed similarly for the second instance, but pay attention to the commands
   and the configuration, as both are slightly different from the steps above.

   From the root of the working copy of `ibc-rs`, create a folder for the second instance:

    ```shell
    $ mkdir relay_b && cd relay_b
    ```

8. Paste the following configuration in a file named `config.toml` in the `relay_b` directory:

    ```toml
    [global]
    timeout = '10s'
    strategy = 'naive'
    log_level = 'error'

    [[chains]]
    id = 'ibc-0'
    rpc_addr = 'tcp://localhost:26657'
    grpc_addr = 'tcp://localhost:9090'
    account_prefix = 'cosmos'
    key_name = 'testkey'
    store_prefix = 'ibc'
    gas = 200000
    clock_drift = '5s'
    trusting_period = '14days'

    [chains.trust_threshold]
    numerator = '1'
    denominator = '3'

    [[chains]]
    id = 'ibc-1'
    rpc_addr = 'tcp://localhost:26557'
    grpc_addr = 'tcp://localhost:9091'
    account_prefix = 'cosmos'
    key_name = 'testkey'
    store_prefix = 'ibc'
    gas = 200000
    clock_drift = '5s'
    trusting_period = '14days'

    [chains.trust_threshold]
    numerator = '1'
    denominator = '3'

    [[connections]]
    a_chain = "ibc-0"
    b_chain = "ibc-1"

    [[connections.paths]]
    a_port = 'transfer'
    b_port = 'transfer'
    ```

9. Create the data folders for both chains:

    ```shell
    $ mkdir -p data/ibc-0/data
    $ mkdir -p data/ibc-1/data
    ```

10. Copy the keys over from the chains `data` directory:

    ```shell
    $ cp ../data/ibc-0/key_seed.json data/ibc-0/
    $ cp ../data/ibc-1/key_seed.json data/ibc-1/
    ```
11. Initialize the light clients:

    ```shell
    $ ../scripts/init-clients config.toml ibc-0 ibc-1
    ```

12. Start the first relayer in the `relay_a` directory:

    ```shell
    $ hermes -c config.toml start ibc-0 ibc-1
    ```
    Take note of the identifier of this first channel created between the two chains, e.g. `channel-0`

13. In another terminal, start the second relayer from the `relay_b` directory:

    ```shell
    $ hermes -c config.toml start ibc-0 ibc-1
    ```
    Take note of the identifier of the second channel created between the two chains, e.g. `channel-1`

14. In yet another terminal:
    Use the `tx raw ft-transfer` command to send packets on the two channels:

    ```shell
    hermes -c relay_a/config.toml tx raw ft-transfer ibc-0 ibc-1 transfer channel-0 9999 1000 -n 2
    hermes -c relay_b/config.toml tx raw ft-transfer ibc-0 ibc-1 transfer channel-1 9999 1000 -n 2
    ```

16. Observe the output on both relayer terminals, verify that the send events are processed, and the `recv_packet` -s are sent out.

17. Query the unreceived packets on `ibc-0` and `ibc-1` for both channels:

    ```shell
    # verify that there are no pending packets on channe-0 in either direction
    hermes -c relay_a/config.toml query packet unreceived-packets ibc-1 ibc-0 transfer channel-0
    hermes -c relay_a/config.toml query packet unreceived-acks    ibc-0 ibc-1 transfer channel-0
    hermes -c relay_a/config.toml query packet unreceived-packets ibc-0 ibc-1 transfer channel-0
    hermes -c relay_a/config.toml query packet unreceived-acks    ibc-1 ibc-0 transfer channel-0
    # verify that there are no pending packets on channe-1 in either direction
    hermes -c relay_b/config.toml query packet unreceived-packets ibc-1 ibc-0 transfer channel-1
    hermes -c relay_b/config.toml query packet unreceived-acks    ibc-0 ibc-1 transfer channel-1
    hermes -c relay_b/config.toml query packet unreceived-packets ibc-0 ibc-1 transfer channel-1
    hermes -c relay_b/config.toml query packet unreceived-acks    ibc-1 ibc-0 transfer channel-1
    ```

    There should be no unreceived packets and acks on both channels:

    ```json
    {
      "status": "success",
      "result": []
    }
    ```

    > The above commands may show some packets if any have been sent before the instances were started (Hermes currently does not flush those).


