
from subprocess import Popen
import logging as l

from .cmd import Config


def start(c: Config) -> Popen:
    full_cmd = f'{c.relayer_cmd} --config {c.config_file} --json start'.split(' ')
    l.debug(' '.join(full_cmd))
    return Popen(full_cmd)
