# Packet Tx Commands

## Fungible token transfer

The `tx raw ft-transfer` command can be used to send ICS-20 fungible token transfer packets.
__NOTE:__ This command is meant to be used for testing the packet features of the relayer.

```shell
USAGE:
    hermes tx raw ft-transfer <OPTIONS>

DESCRIPTION:
    Send a fungible token transfer test transaction (ICS20 MsgTransfer)

POSITIONAL ARGUMENTS:
    src_chain_id              identifier of the source chain
    dest_chain_id             identifier of the destination chain
    src_port_id               identifier of the source port
    src_channel_id            identifier of the source channel
    amount                    amount of coins (samoleans, by default) to send (e.g. `100000`)
    height_offset             timeout in number of blocks since current

FLAGS:
    -d, --denom DENOM         denomination of the coins to send
    -n, --number-msgs NUMBER-MSGS
```

__Example__

Send two transfer packets from the `transfer` module and `channel-0` of `ibc-0` to `ibc-1`. Each transfer if for `9999` samoleans (default denomination) and a timeout offset of `10` blocks. The transfer fee is paid by the relayer account on `ibc-1`.

```shell
$ hermes -c config.toml tx raw ft-transfer ibc-0 ibc-1 transfer channel-0 9999 10 -n 2 | jq
```

```json
{
  "status": "success",
  "result": [
    [
      {
        "SendPacketChannel": {
          "height": "1",
          "packet": {
            "data": "7B22616...",
            "destination_channel": "channel-1",
            "destination_port": "transfer",
            "sequence": 7,
            "source_channel": "channel-0",
            "source_port": "transfer",
            "timeout_height": {
              "revision_height": 25041,
              "revision_number": 1
            },
            "timeout_timestamp": 0
          }
        }
      },
      {
        "SendPacketChannel": {
          "height": "1",
          "packet": {
            "data": "7B22616...",
            "destination_channel": "channel-1",
            "destination_port": "transfer",
            "sequence": 8,
            "source_channel": "channel-0",
            "source_port": "transfer",
            "timeout_height": {
              "revision_height": 25041,
              "revision_number": 1
            },
            "timeout_timestamp": 0
          }
        }
      }
    ]
  ]
}
```

The transfer packets are stored on `ibc-0` and can be relayed.

## Relay receive and timeout packets

The `tx raw packet-recv` command can be used to relay the packets sent but not yet received. If the sent packets have timed out then a timeout packet is sent to the source chain.

```shell
USAGE:
    hermes tx raw packet-recv <OPTIONS>

DESCRIPTION:
    Relay receive or timeout packets

POSITIONAL ARGUMENTS:
    dst_chain_id              identifier of the destination chain
    src_chain_id              identifier of the source chain
    src_port_id               identifier of the source port
    src_channel_id            identifier of the source channel
```

__Example__

Send the two transfer packets to the module bound to the `transfer` port and the `channel-0`'s counterparty on `ibc-1`.

__NOTE__: The relayer prepends a client update message before the receive messages.

```shell
$ hermes -c config.toml tx raw packet-recv ibc-1 ibc-0 transfer channel-0 | jq
```

```json
{
  "status": "success",
  "result": [
    [
      {
        "UpdateClient": {
          "client_id": "07-tendermint-1",
          "client_type": "Tendermint",
          "consensus_height": {
            "revision_height": 25049,
            "revision_number": 0
          },
          "height": "1"
        }
      },
      {
        "WriteAcknowledgementChannel": {
          "ack": "7B22726573756C74223A2241513D3D227D",
          "height": "1",
          "packet": {
            "data": "7B22616...",
            "destination_channel": "channel-1",
            "destination_port": "transfer",
            "sequence": 7,
            "source_channel": "channel-0",
            "source_port": "transfer",
            "timeout_height": {
              "revision_height": 25041,
              "revision_number": 1
            },
            "timeout_timestamp": 0
          }
        }
      },
      {
        "WriteAcknowledgementChannel": {
          "ack": "7B22726573756C74223A2241513D3D227D",
          "height": "1",
          "packet": {
            "data": "7B22616...",
            "destination_channel": "channel-1",
            "destination_port": "transfer",
            "sequence": 8,
            "source_channel": "channel-0",
            "source_port": "transfer",
            "timeout_height": {
              "revision_height": 25041,
              "revision_number": 1
            },
            "timeout_timestamp": 0
          }
        }
      }
    ]
  ]
}
```

Both packets have been relayed to `ibc-1` and acknowledged.

## Relay acknowledgment packets

The `tx raw packet-ack` command can be used to relay acknowledgments to the original source of the packets.

```shell
USAGE:
    hermes tx raw packet-recv <OPTIONS>

DESCRIPTION:
    Relay receive or timeout packets

POSITIONAL ARGUMENTS:
    dst_chain_id              identifier of the destination chain
    src_chain_id              identifier of the source chain
    src_port_id               identifier of the source port
    src_channel_id            identifier of the source channel
```

__Example__

Send the two transfer packets to the module bound to the `transfer` port and the `channel-0`'s counterparty on `ibc-1`.

__NOTE__: The relayer prepends a client update message before the acknowledgments.

```shell
$ hermes -c config.toml tx raw packet-ack ibc-0 ibc-1 transfer channel-1 | jq
```

```json
{
  "status": "success",
  "result": [
    [
      {
        "UpdateClient": {
          "client_id": "07-tendermint-0",
          "client_type": "Tendermint",
          "consensus_height": {
            "revision_height": 25673,
            "revision_number": 1
          },
          "height": "1"
        }
      },
      {
        "AcknowledgePacketChannel": {
          "height": "1",
          "packet": {
            "data": "",
            "destination_channel": "channel-1",
            "destination_port": "transfer",
            "sequence": 7,
            "source_channel": "channel-0",
            "source_port": "transfer",
            "timeout_height": {
              "revision_height": 25041,
              "revision_number": 1
            },
            "timeout_timestamp": 0
          }
        }
      },
      {
        "AcknowledgePacketChannel": {
          "height": "1",
          "packet": {
            "data": "",
            "destination_channel": "channel-1",
            "destination_port": "transfer",
            "sequence": 8,
            "source_channel": "channel-0",
            "source_port": "transfer",
            "timeout_height": {
              "revision_height": 25041,
              "revision_number": 1
            },
            "timeout_timestamp": 0
          }
        }
      }
    ]
  ]
}
```

Both acknowledgments have been received on `ibc-0`.