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
  in your `go.mod` in the `gaia` clone:

```replace github.com/cosmos/cosmos-sdk => /Users/<your>/go/src/github.com/cosmos/cosmos-sdk```

- Now `make build` and `make install` your local copy of `gaia`

In order to test the correct operation during the channel close, perform the steps below.

- The channel should be in state open-open:

- Transfer of 5555 `samoleans` from `ibc-1` to `ibc-0`. This results in a
  Tx to `ibc-1` for a `MsgTransfer` packet.
  Make sure you're not relaying this packet (Hermes should not be running on this path).

  ```shell
  {{#template ../../templates/commands/hermes/tx/ft-transfer_1.md SRC_CHAIN_ID=ibc-0 DST_CHAIN_ID=ibc-1 SRC_PORT_ID=transfer SRC_CHANNEL_ID=channel-1 AMOUNT=5555 OPTIONS= --timeout-height-offset 1000 --denom samoleans}}
  ```

- Now do the first step of channel closing: the channel will transition
to close-open:

    ```shell
    {{#template ../../templates/commands/hermes/tx/chan-close-init_1.md SRC_CHAIN_ID=ibc-1 DST_CHAIN_ID=ibc-0 DST_CONNECTION_ID=connection-0 DST_PORT_ID=transfer SRC_PORT_ID=transfer SRC_CHANNEL_ID=channel-1 DST_CHANNEL_ID=channel-0}}
    ```

- Trigger timeout on close to ibc-1

    ```shell
    {{#template ../../templates/commands/hermes/tx/packet-recv_1.md SRC_CHAIN_ID=ibc-1 DST_CHAIN_ID=ibc-0 SRC_PORT_ID=transfer SRC_CHANNEL_ID=channel-1}}
    ```

- Close the channel

    ```shell
    {{#template ../../templates/commands/hermes/tx/chan-close-confirm_1.md SRC_CHAIN_ID=ibc-0 DST_CHAIN_ID=ibc-1 DST_CONNECTION_ID=connection-1 DST_PORT_ID=transfer SRC_PORT_ID=transfer SRC_CHANNEL_ID=channel-0 DST_CHANNEL_ID=channel-1}}
    ```

- Verify that the two ends are in Close state:

  ```shell
  {{#template ../../templates/commands/hermes/query/channel/end_1.md CHAIN_ID=ibc-0 PORT_ID=transfer CHANNEL_ID=channel-0}}
  {{#template ../../templates/commands/hermes/query/channel/end_1.md CHAIN_ID=ibc-1 PORT_ID=transfer CHANNEL_ID=channel-1}}
  ```

[chan-close]: ../../documentation/commands/tx/channel-close.md#channel-close-init
