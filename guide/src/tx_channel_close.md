# Channel Close Handshake

__Notes__:

The application running on chain may initiate the closing of a channel by sending a `MsgChannelCloseInit` message. The cosmos-sdk implementation does not allow the relayer to initiate the closing of channels. Therefore, when using the Gaia release image, the `chan-close-init` command will fail. The command is rejected by the `cosmos-sdk` transfer module. To
be able to test this:

- Clone the Cosmos SDK

    ```shell script
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

- transfer of 5555 samoleans from `ibc-1` to `ibc-0`. This results in a
  Tx to `ibc-1` for a `MsgTransfer` packet.
  Make sure you're not relaying this packet (the relayer should not be running on
  this path).

  ```shell script
  hermes tx raw ft-transfer ibc-1 ibc-0 transfer channel-1 5555 1000 -n 1 -d samoleans
  ```

## Channel Close Init

Use the `chan-close-init` command to initialize the closure of a channel.

```shell
USAGE:
    hermes tx raw chan-close-init <OPTIONS>

DESCRIPTION:
    Initiate the closing of a channel (ChannelCloseInit)

POSITIONAL ARGUMENTS:
    dst_chain_id              identifier of the destination chain
    src_chain_id              identifier of the source chain
    dst_conn_id               identifier of the destination connection
    dst_port_id               identifier of the destination port
    src_port_id               identifier of the source port

FLAGS:
    -d, --dst-chan-id ID      identifier of the destination channel (required)
    -s, --src-chan-id ID      identifier of the source channel (required)
```

__Example__

```shell
$ hermes tx raw chan-close-init ibc-0 ibc-1 connection-0 transfer transfer -d channel-0 -s channel-1 | jq
```

```json
{
  "status": "success",
  "result": {
    "CloseInitChannel": {
      "channel_id": "channel-1",
      "connection_id": "connection-1",
      "counterparty_channel_id": "channel-3",
      "counterparty_port_id": "transfer",
      "height": "1",
      "port_id": "transfer"
    }
  }
}
```

## Channel Close Confirm

Use the `chan-close-confirm` command to confirm the closure of a channel.

```shell
USAGE:
    hermes tx raw chan-close-confirm <OPTIONS>

DESCRIPTION:
    Confirm the closing of a channel (ChannelCloseConfirm)

POSITIONAL ARGUMENTS:
    dst_chain_id              identifier of the destination chain
    src_chain_id              identifier of the source chain
    dst_conn_id               identifier of the destination connection
    dst_port_id               identifier of the destination port
    src_port_id               identifier of the source port

FLAGS:
    -d, --dst-chan-id ID      identifier of the destination channel (required)
    -s, --src-chan-id ID      identifier of the source channel (required)
```

__Example__

```shell
$ hermes tx raw chan-close-confirm ibc-1 ibc-0 connection-1 transfer transfer -d channel-1 -s channel-0 | jq
```

```json
{
  "status": "success",
  "result": {
    "CloseConfirmChannel": {
      "channel_id": "channel-3",
      "connection_id": "connection-3",
      "counterparty_channel_id": "channel-1",
      "counterparty_port_id": "transfer",
      "height": "1",
      "port_id": "transfer"
    }
  }
}
```
