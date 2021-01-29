#!/usr/bin/env python3

import argparse
import logging as l
from pathlib import Path

import e2e.channel as channel
import e2e.client as client
import e2e.connection as connection
import e2e.packet as packet
from e2e.cmd import Config
from e2e.common import *


def run(c: Config):
    IBC_0 = ChainId('ibc-0')
    IBC_1 = ChainId('ibc-1')

    ibc0_client_id = client.create_update_query_client(c, IBC_0, IBC_1)

    # Allocate first IDs on ibc-1
    ibc1_client_id = client.create_client(c, IBC_1, IBC_0)
    ibc1_conn_id = connection.conn_init(c, IBC_1, IBC_0, ibc1_client_id, ibc0_client_id)
    ibc1_chan_id = channel.chan_open_init(c, dst=IBC_1, src=IBC_0, dst_conn=ibc1_conn_id)

    ibc1_client_id = client.create_update_query_client(c, IBC_1, IBC_0)

    split()

    ibc0_conn_id, ibc1_conn_id = connection.handshake(
        c, IBC_0, IBC_1, ibc0_client_id, ibc1_client_id)

    split()

    ibc0_chan_id, ibc1_chan_id = channel.handshake(
        c, IBC_0, IBC_1, ibc0_conn_id, ibc1_conn_id)

    split()

    packet.ping_pong(c, IBC_0, IBC_1, ibc0_chan_id, ibc1_chan_id)


def main():
    parser = argparse.ArgumentParser(
        description='Test all relayer commands, end-to-end')

    parser.add_argument('-c', '--config',
                        help='configuration file for the relayer',
                        metavar='CONFIG_FILE',
                        required=True,
                        type=Path)

    parser.add_argument('--cmd',
                        help='command to run the relayer (default: cargo run --bin relayer --)',
                        metavar='CMD',
                        default='cargo run --bin relayer --')

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
        format='[%(asctime)s] [%(levelname)8s] %(message)s',
        datefmt='%Y-%m-%d %H:%M:%S')

    run(config)


if __name__ == "__main__":
    main()
