# Clearing Packets

## `clear packets`

This command clears outstanding packets on a given channel in both directions,
by issuing the appropriate [packet-recvs](../tx/packet.md#relay-receive-and-timeout-packets)
and [packet-acks](../tx/packet.md#relay-acknowledgment-packets).

### Usage

```
USAGE:
    hermes clear packets [OPTIONS] --chain <CHAIN_ID> --port <PORT_ID> --channel <CHANNEL_ID>

DESCRIPTION:
    Clear outstanding packets (i.e., packet-recv and packet-ack) on a given channel in both directions.
    The channel is identified by the chain, port, and channel IDs at one of its ends

OPTIONS:
        --counterparty-key-name <COUNTERPARTY_KEY_NAME>
            use the given signing key for the counterparty chain (default: `counterparty_key_name`
            config)

        --key-name <KEY_NAME>
            use the given signing key for the specified chain (default: `key_name` config)

REQUIRED:
        --chain <CHAIN_ID>        Identifier of the chain
        --channel <CHANNEL_ID>    Identifier of the channel
        --port <PORT_ID>          Identifier of the port
```

### Example

1. Without Hermes running, send 3 packets over a channel, here `channel-13`:

```
❯ hermes tx ft-transfer --receiver-chain ibc1 --sender-chain ibc0 --sender-port transfer --sender-channel channel-13 --amount 9999 --timeout-height-offset 1000 --number-msgs 3
2022-02-24T14:16:28.295526Z  INFO ThreadId(01) using default configuration from '/Users/coromac/.hermes/config.toml'
2022-02-24T14:16:28.330860Z  INFO ThreadId(15) send_tx{id=ibc0}: refresh: retrieved account sequence=61 number=1
2022-02-24T14:16:28.350022Z  INFO ThreadId(15) wait_for_block_commits: waiting for commit of tx hashes(s) AE4C3186778488E45670EB7303FA77E69B39F4E7C7494B05EC51E55136A373D6 id=ibc0
Success: [
    SendPacket(
        SendPacket {
            height: Height {
                revision: 0,
                height: 86208,
            },
            packet: Packet {
                sequence: Sequence(
                    14,
                ),
                source_port: PortId(
                    "transfer",
                ),
                source_channel: ChannelId(
                    "channel-13",
                ),
                destination_port: PortId(
                    "transfer",
                ),
                destination_channel: ChannelId(
                    "channel-12",
                ),
                data: [ ... ],
                timeout_height: Height {
                    revision: 0,
                    height: 87203,
                },
                timeout_timestamp: Timestamp {
                    time: None,
                },
            },
        },
    ),
    SendPacket(
        SendPacket {
            height: Height {
                revision: 0,
                height: 86208,
            },
            packet: Packet {
                sequence: Sequence(
                    15,
                ),
                source_port: PortId(
                    "transfer",
                ),
                source_channel: ChannelId(
                    "channel-13",
                ),
                destination_port: PortId(
                    "transfer",
                ),
                destination_channel: ChannelId(
                    "channel-12",
                ),
                data: [ ... ],
                timeout_height: Height {
                    revision: 0,
                    height: 87203,
                },
                timeout_timestamp: Timestamp {
                    time: None,
                },
            },
        },
    ),
    SendPacket(
        SendPacket {
            height: Height {
                revision: 0,
                height: 86208,
            },
            packet: Packet {
                sequence: Sequence(
                    16,
                ),
                source_port: PortId(
                    "transfer",
                ),
                source_channel: ChannelId(
                    "channel-13",
                ),
                destination_port: PortId(
                    "transfer",
                ),
                destination_channel: ChannelId(
                    "channel-12",
                ),
                data: [ ... ],
                timeout_height: Height {
                    revision: 0,
                    height: 87203,
                },
                timeout_timestamp: Timestamp {
                    time: None,
                },
            },
        },
    ),
]
```

2. Because the relayer is not running these packets won't be relayed,
as can be seen with the `query packet pending-sends` command:

```
❯ hermes query packet pending-sends --chain ibc1 --port transfer --channel channel-13
2022-02-24T14:21:28.874190Z  INFO ThreadId(01) using default configuration from '/Users/coromac/.hermes/config.toml'
Success: [
    14,
    15,
    16,
]
```

3. We can clear them manually using the `clear packets` command:

```
❯ hermes clear packets --chain ibc0 --port transfer --channel channel-13
2022-02-24T14:17:25.748422Z  INFO ThreadId(01) using default configuration from '/Users/coromac/.hermes/config.toml'
2022-02-24T14:17:25.799704Z  INFO ThreadId(01) PacketRecvCmd{src_chain=ibc0 src_port=transfer src_channel=channel-13 dst_chain=ibc1}: found unprocessed SendPacket events for [Sequence(14), Sequence(15), Sequence(16)] (first 10 shown here; total=3)
2022-02-24T14:17:25.827177Z  INFO ThreadId(01) PacketRecvCmd{src_chain=ibc0 src_port=transfer src_channel=channel-13 dst_chain=ibc1}: ready to fetch a scheduled op. data with batch of size 3 targeting Destination
2022-02-24T14:17:26.504798Z  INFO ThreadId(01) PacketRecvCmd{src_chain=ibc0 src_port=transfer src_channel=channel-13 dst_chain=ibc1}:relay{odata=E96CV_cA5P ->Destination @0-86218; len=3}: assembled batch of 4 message(s)
2022-02-24T14:17:26.508873Z  INFO ThreadId(29) send_tx{id=ibc1}: refresh: retrieved account sequence=54 number=1
2022-02-24T14:17:26.561715Z  INFO ThreadId(29) wait_for_block_commits: waiting for commit of tx hashes(s) 07AA83524257105CC476063932A560893BE8F4E94C679BFD00F970FC248647E0 id=ibc1
2022-02-24T14:17:31.948950Z  INFO ThreadId(01) PacketRecvCmd{src_chain=ibc0 src_port=transfer src_channel=channel-13 dst_chain=ibc1}:relay{odata=E96CV_cA5P ->Destination @0-86218; len=3}: [Sync->ibc1] result events:
    UpdateClientEv(h: 0-86215, cs_h: 07-tendermint-3(0-86219))
    WriteAcknowledgementEv(WriteAcknowledgement - h:0-86215, seq:14, path:channel-13/transfer->channel-12/transfer, toh:0-87203, tos:Timestamp(NoTimestamp)))
    WriteAcknowledgementEv(WriteAcknowledgement - h:0-86215, seq:15, path:channel-13/transfer->channel-12/transfer, toh:0-87203, tos:Timestamp(NoTimestamp)))
    WriteAcknowledgementEv(WriteAcknowledgement - h:0-86215, seq:16, path:channel-13/transfer->channel-12/transfer, toh:0-87203, tos:Timestamp(NoTimestamp)))


2022-02-24T14:17:31.949192Z  INFO ThreadId(01) PacketRecvCmd{src_chain=ibc0 src_port=transfer src_channel=channel-13 dst_chain=ibc1}:relay{odata=E96CV_cA5P ->Destination @0-86218; len=3}: success
2022-02-24T14:17:31.989215Z  INFO ThreadId(01) PacketAckCmd{src_chain=ibc1 src_port=transfer src_channel=channel-12 dst_chain=ibc0}: found unprocessed WriteAcknowledgement events for [Sequence(14), Sequence(15), Sequence(16)] (first 10 shown here; total=3)
2022-02-24T14:17:32.013500Z  INFO ThreadId(01) PacketAckCmd{src_chain=ibc1 src_port=transfer src_channel=channel-12 dst_chain=ibc0}: ready to fetch a scheduled op. data with batch of size 3 targeting Destination
2022-02-24T14:17:33.211930Z  INFO ThreadId(01) PacketAckCmd{src_chain=ibc1 src_port=transfer src_channel=channel-12 dst_chain=ibc0}:relay{odata=L4fnSXkxL_ ->Destination @0-86215; len=3}: assembled batch of 4 message(s)
2022-02-24T14:17:33.215803Z  INFO ThreadId(15) send_tx{id=ibc0}: refresh: retrieved account sequence=62 number=1
2022-02-24T14:17:33.245229Z  INFO ThreadId(15) wait_for_block_commits: waiting for commit of tx hashes(s) 62C69B1C46AF45182D5D99C6CB5EB301F8A402726772BA4EE067B18C68F2A4D6 id=ibc0
2022-02-24T14:17:37.465489Z  INFO ThreadId(01) PacketAckCmd{src_chain=ibc1 src_port=transfer src_channel=channel-12 dst_chain=ibc0}:relay{odata=L4fnSXkxL_ ->Destination @0-86215; len=3}: [Sync->ibc0] result events:
    UpdateClientEv(h: 0-86221, cs_h: 07-tendermint-3(0-86216))
    AcknowledgePacketEv(h:0-86221, seq:14, path:channel-13/transfer->channel-12/transfer, toh:0-87203, tos:Timestamp(NoTimestamp)))
    AcknowledgePacketEv(h:0-86221, seq:15, path:channel-13/transfer->channel-12/transfer, toh:0-87203, tos:Timestamp(NoTimestamp)))
    AcknowledgePacketEv(h:0-86221, seq:16, path:channel-13/transfer->channel-12/transfer, toh:0-87203, tos:Timestamp(NoTimestamp)))


2022-02-24T14:17:37.465802Z  INFO ThreadId(01) PacketAckCmd{src_chain=ibc1 src_port=transfer src_channel=channel-12 dst_chain=ibc0}:relay{odata=L4fnSXkxL_ ->Destination @0-86215; len=3}: success
Success: [
    UpdateClient(
        UpdateClient {
            common: Attributes {
                height: Height {
                    revision: 0,
                    height: 86215,
                },
                client_id: ClientId(
                    "07-tendermint-3",
                ),
                client_type: Tendermint,
                consensus_height: Height {
                    revision: 0,
                    height: 86219,
                },
            },
            header: Some(
                Tendermint(
                     Header {...},
                ),
            ),
        },
    ),
    WriteAcknowledgement(
        WriteAcknowledgement {
            height: Height {
                revision: 0,
                height: 86215,
            },
            packet: Packet {
                sequence: Sequence(
                    14,
                ),
                source_port: PortId(
                    "transfer",
                ),
                source_channel: ChannelId(
                    "channel-13",
                ),
                destination_port: PortId(
                    "transfer",
                ),
                destination_channel: ChannelId(
                    "channel-12",
                ),
                data: [ ... ],
                timeout_height: Height {
                    revision: 0,
                    height: 87203,
                },
                timeout_timestamp: Timestamp {
                    time: None,
                },
            },
            ack: [ ... ],
        },
    ),
    WriteAcknowledgement(
        WriteAcknowledgement {
            height: Height {
                revision: 0,
                height: 86215,
            },
            packet: Packet {
                sequence: Sequence(
                    15,
                ),
                source_port: PortId(
                    "transfer",
                ),
                source_channel: ChannelId(
                    "channel-13",
                ),
                destination_port: PortId(
                    "transfer",
                ),
                destination_channel: ChannelId(
                    "channel-12",
                ),
                data: [ ... ],
                timeout_height: Height {
                    revision: 0,
                    height: 87203,
                },
                timeout_timestamp: Timestamp {
                    time: None,
                },
            },
            ack: [ ... ],
        },
    ),
    WriteAcknowledgement(
        WriteAcknowledgement {
            height: Height {
                revision: 0,
                height: 86215,
            },
            packet: Packet {
                sequence: Sequence(
                    16,
                ),
                source_port: PortId(
                    "transfer",
                ),
                source_channel: ChannelId(
                    "channel-13",
                ),
                destination_port: PortId(
                    "transfer",
                ),
                destination_channel: ChannelId(
                    "channel-12",
                ),
                data: [ ... ],
                timeout_height: Height {
                    revision: 0,
                    height: 87203,
                },
                timeout_timestamp: Timestamp {
                    time: None,
                },
            },
            ack: [ ... ],
        },
    ),
    UpdateClient(
        UpdateClient {
            common: Attributes {
                height: Height {
                    revision: 0,
                    height: 86221,
                },
                client_id: ClientId(
                    "07-tendermint-3",
                ),
                client_type: Tendermint,
                consensus_height: Height {
                    revision: 0,
                    height: 86216,
                },
            },
            header: Some(
                Tendermint(
                     Header {...},
                ),
            ),
        },
    ),
    AcknowledgePacket(
        AcknowledgePacket {
            height: Height {
                revision: 0,
                height: 86221,
            },
            packet: Packet {
                sequence: Sequence(
                    14,
                ),
                source_port: PortId(
                    "transfer",
                ),
                source_channel: ChannelId(
                    "channel-13",
                ),
                destination_port: PortId(
                    "transfer",
                ),
                destination_channel: ChannelId(
                    "channel-12",
                ),
                data: [],
                timeout_height: Height {
                    revision: 0,
                    height: 87203,
                },
                timeout_timestamp: Timestamp {
                    time: None,
                },
            },
        },
    ),
    AcknowledgePacket(
        AcknowledgePacket {
            height: Height {
                revision: 0,
                height: 86221,
            },
            packet: Packet {
                sequence: Sequence(
                    15,
                ),
                source_port: PortId(
                    "transfer",
                ),
                source_channel: ChannelId(
                    "channel-13",
                ),
                destination_port: PortId(
                    "transfer",
                ),
                destination_channel: ChannelId(
                    "channel-12",
                ),
                data: [],
                timeout_height: Height {
                    revision: 0,
                    height: 87203,
                },
                timeout_timestamp: Timestamp {
                    time: None,
                },
            },
        },
    ),
    AcknowledgePacket(
        AcknowledgePacket {
            height: Height {
                revision: 0,
                height: 86221,
            },
            packet: Packet {
                sequence: Sequence(
                    16,
                ),
                source_port: PortId(
                    "transfer",
                ),
                source_channel: ChannelId(
                    "channel-13",
                ),
                destination_port: PortId(
                    "transfer",
                ),
                destination_channel: ChannelId(
                    "channel-12",
                ),
                data: [],
                timeout_height: Height {
                    revision: 0,
                    height: 87203,
                },
                timeout_timestamp: Timestamp {
                    time: None,
                },
            },
        },
    ),
]
```

4. The packets have now been successfully relayed:

```
❯ hermes query packet pending-sends --chain ibc1 --port transfer --channel channel-13
2022-02-24T14:21:28.874190Z  INFO ThreadId(01) using default configuration from '/Users/coromac/.hermes/config.toml'
Success: []
```
