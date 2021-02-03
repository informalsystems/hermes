[WIP]
# Channel Close Handshake

__Note__: 
The application running on chain may initiate the closing of a channel by sending a `MsgChannelCloseInit` message. The cosmos-sdk implementation does not allow the relayer to initiate the closing of channels. Therefore, when using the Gaia release image, the `chan-close-init` command will fail. The command is rejected by the `cosmos-sdk` transfer module. To
be able to test this:
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

In order to test the correct operation during the channel close, perform the steps below.

- transfer of 5555 samoleans from `ibc-1` to `ibc-0`. This results in a
  Tx to `ibc-1` for a `MsgTransfer` packet.
  Make sure you're not relaying this packet (the relayer should not be running on
  this path).

```shell script
hermes tx raw ft-transfer ibc-1 ibc-0 transfer channel-1 5555 1000 -n 1 -d samoleans
```

Starting with channel in open-open:

- close-open

    ```shell script
    hermes tx raw chan-close-init ibc-0 ibc-1 connection-0 transfer transfer channel-0 channel-1
    ```

- trigger timeout on close to ibc-1

    ```shell script
    hermes tx raw packet-recv ibc-0 ibc-1 transfer channel-1
    ```

- close-close

    ```shell script
    hermes tx raw chan-close-confirm ibc-1 ibc-0 connection-1 transfer transfer channel-1 channel-0
    ```

- verify that the two ends are in Close state:

  ```shell script
  hermes query channel end ibc-0 transfer channel-0
  hermes query channel end ibc-1 transfer channel-1
  ```
