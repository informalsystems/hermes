# Patch Gaia

The guide below refers specifically to patching your gaia chain so that the
relayer can initiate the closing of channels by submitting a [`ChanCloseInit`][chan-close] message.
Without this modification, the transaction will be rejected.
We also describe how to test the channel closing feature.

- Clone the Cosmos SDK

    ```shell
    git clone https://github.com/cosmos/cosmos-sdk.git ~/go/src/github.com/cosmos/cosmos-sdk
    cd ~/go/src/github.com/cosmos/cosmos-sdk
    ```

- Apply these diffs:

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

- Append the line below (watch for the placeholder `<your>`) as the last line
  in your `go.mod` in the gaia clone:

```replace github.com/cosmos/cosmos-sdk => /Users/<your>/go/src/github.com/cosmos/cosmos-sdk```

- Now `make build` and `make install` your local copy of gaia

In order to test the correct operation during the channel close, perform the steps below.

- The channel should be in state open-open:

- Transfer of 5555 samoleans from `ibc-1` to `ibc-0`. This results in a
  Tx to `ibc-1` for a `MsgTransfer` packet.
  Make sure you're not relaying this packet (the relayer should not be running on
  this path).

  ```shell
  hermes tx ft-transfer --receiver-chain ibc-0 --sender-chain ibc-1 --sender-port transfer --sender-channel channel-1 --amount 5555 --timeout-height-offset 1000 --number-msgs 1 --denom samoleans
  ```

- Now do the first step of channel closing: the channel will transition
to close-open:

    ```shell
    hermes --config config.toml tx chan-close-init --receiver-chain ibc-0 --sender-chain ibc-1 --receiver-connection connection-0 --receiver-port transfer --sender-port transfer --receiver-channel channel-0 --sender-channel channel-1
    ```

- Trigger timeout on close to ibc-1

    ```shell
    hermes --config config.toml tx packet-recv --receiver-chain ibc-0 --sender-chain ibc-1 --sender-port transfer --sender-channel channel-1
    ```

- Close the channel

    ```shell
    hermes --config config.toml tx chan-close-confirm --receiver-chain ibc-1 --sender-chain ibc-0 --receiver-connection connection-1 --receiver-port transfer --sender-port transfer --receiver-channel channel-1 --sender-channel channel-0
    ```

- Verify that the two ends are in Close state:

  ```shell
  hermes --config config.toml query channel end --chain ibc-0 --port transfer --channel channel-0
  hermes --config config.toml query channel end --chain ibc-1 --port transfer --channel channel-1
  ```

[chan-close]: ../../documentation/commands/tx/channel-close.md#channel-close-init
