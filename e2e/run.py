#!/usr/bin/env python3

import argparse
import logging as l

from pathlib import Path

import e2e.channel as channel
import e2e.client as client
import e2e.connection as connection
import e2e.packet as packet
import e2e.relayer as relayer
from e2e.cmd import Config
from e2e.common import *


def loop(c: Config):
    IBC_0 = ChainId('ibc-0')
    IBC_1 = ChainId('ibc-1')

    TRANSFER = PortId('transfer')
    IBC_0_CHANNEL = ChannelId('channel-0')
    IBC_1_CHANNEL = ChannelId('channel-1')

    # 1. create some unreceived acks

    # hermes tx raw ft-transfer ibc-1 ibc-0 transfer channel-0 10000 1000 -n 2
    packet.packet_send(c, src=IBC_0, dst=IBC_1, src_port=TRANSFER,
                       src_channel=IBC_0_CHANNEL, amount=10000, height_offset=1000, number_msgs=2,
                       key='user2')

    # hermes tx raw ft-transfer ibc-0 ibc-1 transfer channel-1 10000 1000 -n 2
    packet.packet_send(c, src=IBC_1, dst=IBC_0, src_port=TRANSFER,
                       src_channel=IBC_1_CHANNEL, amount=10000, height_offset=1000, number_msgs=2,
                       key='user2')
    sleep(5.0)

    # hermes tx raw packet-recv ibc-1 ibc-0 transfer channel-0
    packet.packet_recv(c, src=IBC_0, dst=IBC_1,
                       src_port=TRANSFER, src_channel=IBC_0_CHANNEL)

    # hermes tx raw packet-recv ibc-0 ibc-1 transfer channel-1
    packet.packet_recv(c, src=IBC_1, dst=IBC_0,
                       src_port=TRANSFER, src_channel=IBC_1_CHANNEL)

    # 2. create some unreceived packets

    # hermes tx raw ft-transfer ibc-0 ibc-1 transfer channel-1 10000 1000 -n 3
    packet.packet_send(c, src=IBC_1, dst=IBC_0, src_port=TRANSFER,
                       src_channel=IBC_1_CHANNEL, amount=10000, height_offset=1000, number_msgs=3,
                       key='user2')

    # hermes tx raw ft-transfer ibc-1 ibc-0 transfer channel-0 10000 1000 -n 4
    packet.packet_send(c, src=IBC_0, dst=IBC_1, src_port=TRANSFER,
                       src_channel=IBC_0_CHANNEL, amount=10000, height_offset=1000, number_msgs=4,
                       key='user2')

    sleep(10.0)

    # 3. verify the expected number of unreceived packets and acks on each channel end

    # hermes query packet unreceived-packets ibc-0 transfer channel-0
    unreceived = packet.query_unreceived_packets(
        c, chain=IBC_0, port=TRANSFER, channel=IBC_0_CHANNEL)

    assert (len(unreceived) == 3), (unreceived, "unreceived packet mismatch")

    # hermes query packet unreceived-acks ibc-1 transfer channel-1
    unreceived = packet.query_unreceived_acks(
        c, chain=IBC_1, port=TRANSFER, channel=IBC_1_CHANNEL)

    assert (len(unreceived) == 2), (unreceived, "unreceived packet mismatch")

    # hermes query packet unreceived-packets ibc-1 transfer channel-1
    unreceived = packet.query_unreceived_packets(
        c, chain=IBC_1, port=TRANSFER, channel=IBC_1_CHANNEL)

    assert (len(unreceived) == 4), (unreceived, "unreceived packet mismatch")

    # hermes query packet unreceived-acks ibc-0 transfer channel-0
    unreceived = packet.query_unreceived_acks(
        c, chain=IBC_0, port=TRANSFER, channel=IBC_0_CHANNEL)

    assert (len(unreceived) == 2), (unreceived, "unreceived packet mismatch")

    sleep(5.0)

    # 4. start relaying - it should clear the unreceived packets
    proc = relayer.start(c)

    sleep(5.0)

    # 5. wait a bit and make sure there are no pending packets

    # hermes tx raw ft-transfer ibc-0 ibc-1 transfer channel-1 10000 1000 -n 3
    packet.packet_send(c, src=IBC_1, dst=IBC_0, src_port=TRANSFER,
                       src_channel=IBC_1_CHANNEL, amount=10000, height_offset=1000, number_msgs=3,
                       key='user2')

    # hermes tx raw ft-transfer ibc-1 ibc-0 transfer channel-0 10000 1000 -n 4
    packet.packet_send(c, src=IBC_0, dst=IBC_1, src_port=TRANSFER,
                       src_channel=IBC_0_CHANNEL, amount=10000, height_offset=1000, number_msgs=4,
                       key='user2')

    sleep(10.0)

    # hermes query packet unreceived-packets ibc-1 transfer channel-1
    unreceived = packet.query_unreceived_packets(
        c, chain=IBC_1, port=TRANSFER, channel=IBC_1_CHANNEL)

    assert (len(unreceived) == 0), (unreceived, "unreceived packets mismatch (expected 0)")

    # hermes query packet unreceived-acks ibc-1 transfer channel-1
    unreceived = packet.query_unreceived_acks(
        c, chain=IBC_1, port=TRANSFER, channel=IBC_1_CHANNEL)

    assert (len(unreceived) == 0), (unreceived, "unreceived acks mismatch (expected 0)")

    # hermes query packet unreceived-packets ibc-0 transfer channel-0
    unreceived = packet.query_unreceived_packets(
        c, chain=IBC_0, port=TRANSFER, channel=IBC_0_CHANNEL)

    assert (len(unreceived) == 0), (unreceived, "unreceived packets mismatch (expected 0)")

    # hermes query packet unreceived-acks ibc-0 transfer channel-0
    unreceived = packet.query_unreceived_acks(
        c, chain=IBC_0, port=TRANSFER, channel=IBC_0_CHANNEL)

    assert (len(unreceived) == 0), (unreceived, "unreceived acks mismatch (expected 0)")

    # 6. All good, stop the relayer
    proc.kill()


def raw(c: Config):
    IBC_0 = ChainId('ibc-0')
    IBC_1 = ChainId('ibc-1')

    ibc0_client_id = client.create_update_query_client(c, IBC_0, IBC_1)

    # Allocate first IDs on ibc-1
    ibc1_client_id = client.create_update_query_client(c, IBC_1, IBC_0)
    ibc1_conn_id = connection.conn_init(
        c, IBC_1, IBC_0, ibc1_client_id, ibc0_client_id)
    ibc1_chan_id = channel.chan_open_init(
        c, dst=IBC_1, src=IBC_0, dst_conn=ibc1_conn_id)

    ibc1_client_id = client.create_update_query_client(c, IBC_1, IBC_0)

    split()

    ibc0_conn_id, ibc1_conn_id = connection.handshake(
        c, IBC_0, IBC_1, ibc0_client_id, ibc1_client_id)

    split()

    ibc0_chan_id, ibc1_chan_id = channel.handshake(
        c, IBC_0, IBC_1, ibc0_conn_id, ibc1_conn_id)

    split()

    packet.ping_pong(c, IBC_0, IBC_1, ibc0_chan_id, ibc1_chan_id)

    split()

    sleep(5)

    packet.timeout(c, IBC_0, IBC_1, ibc0_chan_id, ibc1_chan_id)

    split()

    # The ChannelCloseInit message is currently denied by Gaia,
    # and requires a patch to be accepted.
    # channel.close(c, IBC_0, IBC_1, ibc0_conn_id,
    #               ibc1_conn_id, ibc0_chan_id, ibc1_chan_id)


def main():
    parser = argparse.ArgumentParser(
        description='Test all relayer commands, end-to-end')

    parser.add_argument('-c', '--config',
                        help='configuration file for the relayer',
                        metavar='CONFIG_FILE',
                        required=True,
                        type=Path)

    parser.add_argument('--cmd',
                        help='command to run the relayer (default: cargo run --bin hermes --)',
                        metavar='CMD',
                        default='cargo run --bin hermes --')

    parser.add_argument('--log-level',
                        help='minimum log level (default: debug)',
                        metavar='LOG',
                        choices=['notset', 'debug', 'info',
                                 'warning', 'error', 'critical'],
                        default='debug')

    args = parser.parse_args()

    if not args.config.exists():
        print(
            f'error: supplied configuration file does not exist: {args.config}')
        exit(1)

    config = Config(config_file=args.config, relayer_cmd=args.cmd,
                    log_level=args.log_level.upper())

    l.basicConfig(
        level=config.log_level,
        format='%(asctime)s [%(levelname)8s] %(message)s',
        datefmt='%Y-%m-%d %H:%M:%S')

    raw(config)
    loop(config)


if __name__ == "__main__":
    main()
