# Fungible token transfer with fees

Use the `fee transfer` command to send an `IncentivizedPacket`.

```shell
{{#include ../../../templates/help_templates/fee/transfer.md}}
```

__Example__

Send a transfer packet from the `transfer` module and `channel-0` of `ibc-0` to `ibc-1`. Each transfer is for `9999` `samoleans` (default denomination), ICS29 fees of 50 `samoleans` for `recv_fee`, 25 `samoleans` for `ack_fee`, `10` `samoleans` for `timeout_fee` and a timeout offset of `10` blocks. The transfer fee is paid by the associated account on `ibc-1`.

```shell
{{#template ../../../templates/commands/hermes/fee/transfer_1.md DST_CHAIN_ID=ibc-1 SRC_CHAIN_ID=ibc-0 SRC_PORT_ID=transfer SRC_CHANNEL_ID=channel-0 AMOUNT=9999 OPTIONS=  --receive-fee 50 --ack-fee 25 --timeout-fee 10 --timeout-height-offset 1000}}
```

```json
SUCCESS [
    IbcEventWithHeight {
        event: IncentivizedPacket(
            IncentivizedPacket {
                port_id: PortId(
                    "transfer",
                ),
                channel_id: ChannelId(
                    "channel-0",
                ),
                sequence: Sequence(
                    8,
                ),
                total_recv_fee: [
                    Coin {
                        denom: "stake",
                        amount: Amount(
                            50,
                        ),
                    },
                ],
                total_ack_fee: [
                    Coin {
                        denom: "stake",
                        amount: Amount(
                            25,
                        ),
                    },
                ],
                total_timeout_fee: [
                    Coin {
                        denom: "stake",
                        amount: Amount(
                            10,
                        ),
                    },
                ],
            },
        ),
        height: Height {
            revision: 1,
            height: 1574,
        },
    },
    IbcEventWithHeight {
        event: SendPacket(
            SendPacket {
                packet: Packet {
                    sequence: Sequence(
                        8,
                    ),
                    source_port: PortId(
                        "transfer",
                    ),
                    source_channel: ChannelId(
                        "channel-0",
                    ),
                    destination_port: PortId(
                        "transfer",
                    ),
                    destination_channel: ChannelId(
                        "channel-0",
                    ),
                    data: [123, 34, 97, 109, 111, 117, 110, 116, 34, 58, 34, 49, 48, 48, 48, 34, 44, 34, 100, 101, 110, 111, 109, 34, 58, 34, 115, 116, 97, 107, 101, 34, 44, 34, 114, 101, 99, 101, 105, 118, 101, 114, 34, 58, 34, 99, 111, 115, 109, 111, 115, 49, 52, 122, 115, 50, 120, 51, 56, 108, 109, 107, 119, 52, 101, 113, 118, 108, 51, 108, 112, 109, 108, 53, 108, 56, 99, 114, 122, 97, 120, 110, 54, 109, 55, 119, 117, 122, 110, 120, 34, 44, 34, 115, 101, 110, 100, 101, 114, 34, 58, 34, 99, 111, 115, 109, 111, 115, 49, 109, 57, 108, 51, 53, 56, 120, 117, 110, 104, 104, 119, 100, 115, 48, 53, 54, 56, 122, 97, 52, 57, 109, 122, 104, 118, 117, 120, 120, 57, 117, 120, 114, 101, 53, 116, 117, 100, 34, 125],
                    timeout_height: Never,
                    timeout_timestamp: Timestamp {
                        time: Some(
                            Time(
                                2023-03-22 11:49:54.491498,
                            ),
                        ),
                    },
                },
            },
        ),
        height: Height {
            revision: 1,
            height: 1574,
        },
    },
]
```