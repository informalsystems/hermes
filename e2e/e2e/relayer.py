
from subprocess import Popen
import logging as l
from typing import Optional

from .cmd import Config
from .common import ChainId, PortId, ChannelId


def start(c: Config, src: ChainId, dst: ChainId, src_port: Optional[PortId], src_channel: Optional[ChannelId]) -> Popen:
    args = [str(src), str(dst)]
    if src_port != None:
        args.extend(['-p', str(src_port)])
    if src_channel != None:
        args.extend(['-c', str(src_channel)])

    full_cmd = f'{c.relayer_cmd} -c {c.config_file} --json start'.split(' ')
    full_cmd.extend(args)

    l.debug(' '.join(full_cmd))

    return Popen(full_cmd)
