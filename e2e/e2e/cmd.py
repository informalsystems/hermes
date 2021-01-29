#!/usr/bin/env python3

from typing import Any, List, Optional, TypeVar, Generic, Type, Callable, Tuple, NewType

import json
import subprocess

import logging as l

from pathlib import Path
from dataclasses import dataclass, fields as datafields, is_dataclass


@dataclass
class Config:
    config_file: Path
    relayer_cmd: str
    log_level: str


T = TypeVar('T')


@dataclass
class CmdResult(Generic[T]):
    cmd: 'Cmd'
    result: Any

    def success(self) -> T:
        status = self.result.get('status') or 'unknown'
        result = self.result.get('result') or {}

        if status == "success":
            data = self.cmd.process(result)
            l.debug(str(data))
            return data
        else:
            raise ExpectedSuccess(self.cmd, status, result)


class Cmd(Generic[T]):
    name: str

    def process(self, result: Any) -> Any:
        raise NotImplementedError("Cmd::process")

    def args(self) -> List[str]:
        raise NotImplementedError("Cmd::args")

    def to_cmd(self) -> str:
        return f"{self.name} {' '.join(self.args())}"

    def run(self, config: Config) -> CmdResult[T]:
        full_cmd = f'{config.relayer_cmd} -c {config.config_file}'.split(' ')
        full_cmd.extend(self.name.split(' '))
        full_cmd.extend(self.args())
        l.debug(' '.join(full_cmd))

        res = subprocess.run(full_cmd, capture_output=True, text=True)
        lines = res.stdout.splitlines()
        last_line = ''.join(lines[-1:])
        l.debug(last_line)

        return CmdResult(cmd=self, result=json.loads(last_line))


C = TypeVar('C', bound=Cmd)


def cmd(name: str) -> Callable[[Type[C]], Type[C]]:
    def decorator(klass: Type[C]) -> Type[C]:
        klass.name = name
        return klass

    return decorator


def from_dict(klass, dikt) -> Any:
    if is_dataclass(klass):
        fields = datafields(klass)
        args = {f.name: from_dict(f.type, dikt[f.name]) for f in fields}
        return klass(**args)
    else:
        return dikt


class ExpectedSuccess(Exception):
    cmd: Any
    status: str
    result: Any

    def __init__(self, cmd: Any, status: str, result: Any) -> None:
        self.cmd = cmd
        self.status = status
        self.result = result

        super().__init__(
            f"Command '{cmd}' failed. Expected 'success', got '{status}'. Message: {result}"
        )
