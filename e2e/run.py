#!/usr/bin/env python3

import argparse
import logging as l
from typing import Tuple
from pathlib import Path
import toml

import e2e.channel as channel
import e2e.client as client
import e2e.connection as connection
import e2e.packet as packet
import e2e.relayer as relayer
from e2e.cmd import Config
from e2e.common import *


def passive_packets(
        c: Config,
        ibc0: ChainId, ibc1: ChainId, port_id: PortId,
        ibc0_channel_id: ChannelId, ibc1_channel_id: ChannelId):

    # 1. create some unreceived acks

    # hermes tx raw ft-transfer ibc-1 ibc-0 transfer channel-0 10000 -o 1000 -n 2
    packet.packet_send(c, src=ibc0, dst=ibc1, src_port=port_id,
                       src_channel=ibc0_channel_id, amount=10000, height_offset=1000, number_msgs=2)

    # hermes tx raw ft-transfer ibc-0 ibc-1 transfer channel-1 10000 -o 1000 -n 2
    packet.packet_send(c, src=ibc1, dst=ibc0, src_port=port_id,
                       src_channel=ibc1_channel_id, amount=10000, height_offset=1000, number_msgs=2)
    sleep(5.0)

    # hermes tx raw packet-recv ibc-1 ibc-0 transfer channel-0
    packet.packet_recv(c, src=ibc0, dst=ibc1,
                       src_port=port_id, src_channel=ibc0_channel_id)

    # hermes tx raw packet-recv ibc-0 ibc-1 transfer channel-1
    packet.packet_recv(c, src=ibc1, dst=ibc0,
                       src_port=port_id, src_channel=ibc1_channel_id)

    # 2. create some unreceived packets

    # hermes tx raw ft-transfer ibc-0 ibc-1 transfer channel-1 10000 -o 1000 -n 3
    packet.packet_send(c, src=ibc1, dst=ibc0, src_port=port_id,
                       src_channel=ibc1_channel_id, amount=10000, height_offset=1000, number_msgs=3)

    # hermes tx raw ft-transfer ibc-1 ibc-0 transfer channel-0 10000 -o 1000 -n 4
    packet.packet_send(c, src=ibc0, dst=ibc1, src_port=port_id,
                       src_channel=ibc0_channel_id, amount=10000, height_offset=1000, number_msgs=4)

    sleep(10.0)

    # 3. verify the expected number of unreceived packets and acks on each channel end

    # hermes query packet unreceived-packets ibc-0 transfer channel-0
    unreceived = packet.query_unreceived_packets(
        c, chain=ibc0, port=port_id, channel=ibc0_channel_id)

    assert (len(unreceived) == 3), (unreceived, "unreceived packet mismatch")

    # hermes query packet unreceived-acks ibc-1 transfer channel-1
    unreceived = packet.query_unreceived_acks(
        c, chain=ibc1, port=port_id, channel=ibc1_channel_id)

    assert (len(unreceived) == 2), (unreceived, "unreceived packet mismatch")

    # hermes query packet unreceived-packets ibc-1 transfer channel-1
    unreceived = packet.query_unreceived_packets(
        c, chain=ibc1, port=port_id, channel=ibc1_channel_id)

    assert (len(unreceived) == 4), (unreceived, "unreceived packet mismatch")

    # hermes query packet unreceived-acks ibc-0 transfer channel-0
    unreceived = packet.query_unreceived_acks(
        c, chain=ibc0, port=port_id, channel=ibc0_channel_id)

    assert (len(unreceived) == 2), (unreceived, "unreceived packet mismatch")

    # 4. start relaying - it should clear the unreceived packets
    proc = relayer.start(c)

    # 5. wait for the relayer to initialize and pick up pending packets
    sleep(20.0)

    # 6. verify that there are no pending packets
    # hermes query packet unreceived-packets ibc-1 transfer channel-1
    unreceived = packet.query_unreceived_packets(
        c, chain=ibc1, port=port_id, channel=ibc1_channel_id)

    assert (len(unreceived) == 0), (unreceived,
                                    "unreceived packets mismatch (expected 0)")

    # hermes query packet unreceived-acks ibc-1 transfer channel-1
    unreceived = packet.query_unreceived_acks(
        c, chain=ibc1, port=port_id, channel=ibc1_channel_id)

    assert (len(unreceived) == 0), (unreceived,
                                    "unreceived acks mismatch (expected 0)")

    # hermes query packet unreceived-packets ibc-0 transfer channel-0
    unreceived = packet.query_unreceived_packets(
        c, chain=ibc0, port=port_id, channel=ibc0_channel_id)

    assert (len(unreceived) == 0), (unreceived,
                                    "unreceived packets mismatch (expected 0)")

    # hermes query packet unreceived-acks ibc-0 transfer channel-0
    unreceived = packet.query_unreceived_acks(
        c, chain=ibc0, port=port_id, channel=ibc0_channel_id)

    assert (len(unreceived) == 0), (unreceived,
                                    "unreceived acks mismatch (expected 0)")

    # 7. send some packets
    # hermes tx raw ft-transfer ibc-0 ibc-1 transfer channel-1 10000 1000 -n 3
    packet.packet_send(c, src=ibc1, dst=ibc0, src_port=port_id,
                       src_channel=ibc1_channel_id, amount=10000, height_offset=1000, number_msgs=3)

    # hermes tx raw ft-transfer ibc-1 ibc-0 transfer channel-0 10000 1000 -n 4
    packet.packet_send(c, src=ibc0, dst=ibc1, src_port=port_id,
                       src_channel=ibc0_channel_id, amount=10000, height_offset=1000, number_msgs=4)

    sleep(20.0)

    # 8. verify that there are no pending packets
    # hermes query packet unreceived-packets ibc-1 transfer channel-1
    unreceived = packet.query_unreceived_packets(
        c, chain=ibc1, port=port_id, channel=ibc1_channel_id)

    assert (len(unreceived) == 0), (unreceived,
                                    "unreceived packets mismatch (expected 0)")

    # hermes query packet unreceived-acks ibc-1 transfer channel-1
    unreceived = packet.query_unreceived_acks(
        c, chain=ibc1, port=port_id, channel=ibc1_channel_id)

    assert (len(unreceived) == 0), (unreceived,
                                    "unreceived acks mismatch (expected 0)")

    # hermes query packet unreceived-packets ibc-0 transfer channel-0
    unreceived = packet.query_unreceived_packets(
        c, chain=ibc0, port=port_id, channel=ibc0_channel_id)

    assert (len(unreceived) == 0), (unreceived,
                                    "unreceived packets mismatch (expected 0)")

    # hermes query packet unreceived-acks ibc-0 transfer channel-0
    unreceived = packet.query_unreceived_acks(
        c, chain=ibc0, port=port_id, channel=ibc0_channel_id)

    assert (len(unreceived) == 0), (unreceived,
                                    "unreceived acks mismatch (expected 0)")

    # 9.Stop the relayer
    proc.kill()


def raw(c: Config, ibc0: ChainId, ibc1: ChainId, port_id: PortId) -> Tuple[ClientId, ConnectionId, ChannelId, ClientId, ConnectionId, ChannelId]:
    ibc0_client_id = client.create_update_query_client(c, ibc0, ibc1)

    # Allocate first IDs on ibc-1
    ibc1_client_id = client.create_update_query_client(c, ibc1, ibc0)
    ibc1_conn_id = connection.conn_init(
        c, ibc1, ibc0, ibc1_client_id, ibc0_client_id)
    ibc1_chan_id = channel.chan_open_init(
        c, dst=ibc1, src=ibc0, dst_conn=ibc1_conn_id)

    ibc1_client_id = client.create_update_query_client(c, ibc1, ibc0)

    split()

    ibc0_conn_id, ibc1_conn_id = connection.handshake(
        c, ibc0, ibc1, ibc0_client_id, ibc1_client_id)

    split()

    ibc0_chan_id, ibc1_chan_id = channel.handshake(
        c, ibc0, ibc1, ibc0_conn_id, ibc1_conn_id, port_id)

    split()

    packet.ping_pong(c, ibc0, ibc1, ibc0_chan_id, ibc1_chan_id)

    split()

    sleep(5)

    packet.timeout(c, ibc0, ibc1, ibc0_chan_id, ibc1_chan_id)

    split()

    # The ChannelCloseInit message is currently denied by Gaia,
    # and requires a patch to be accepted.
    # channel.close(c, ibc0, ibc1, ibc0_conn_id,
    #               ibc1_conn_id, ibc0_chan_id, ibc1_chan_id)

    return ibc0_client_id, ibc0_conn_id, ibc0_chan_id, ibc1_client_id, ibc1_conn_id, ibc1_chan_id


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

    chains = toml.load(config.config_file)['chains']

    ibc0 = chains[0]['id']
    ibc1 = chains[1]['id']
    port_id = PortId('transfer')

    ibc0_client_id, ibc0_conn_id, ibc0_chan_id, ibc1_client_id, ibc1_conn_id, ibc1_chan_id = raw(
        config, ibc0, ibc1, port_id)
    sleep(2.0)

    passive_packets(config, ibc0, ibc1, port_id, ibc0_chan_id, ibc1_chan_id)
    sleep(2.0)

    connection.passive_connection_init_then_start(
        config, ibc1, ibc0, ibc1_client_id, ibc0_client_id)
    sleep(2.0)

    connection.passive_connection_start_then_init(
        config, ibc1, ibc0, ibc1_client_id, ibc0_client_id)
    sleep(2.0)

    connection.passive_connection_try_then_start(
        config, ibc1, ibc0, ibc1_client_id, ibc0_client_id)
    sleep(2.0)

    channel.passive_channel_start_then_init(
        config, ibc1, ibc0, ibc1_conn_id, port_id)
    sleep(2.0)

    channel.passive_channel_init_then_start(
        config, ibc1, ibc0, ibc1_conn_id, port_id)
    sleep(2.0)

    channel.passive_channel_try_then_start(
        config, ibc1, ibc0, ibc1_conn_id, ibc0_conn_id, port_id)
    sleep(2.0)


if __name__ == "__main__":
    main()
