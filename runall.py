#!/usr/bin/env python3

from typing import Any, List, Optional, TypedDict, TypeVar, Generic, Type, Callable

import os
import json
import subprocess

import logging as l

from time import sleep
from dataclasses import dataclass, fields as datafields, is_dataclass

class ExpectedSuccess(Exception):
    cmd: 'Cmd'
    status: str
    result: Any

    def __init__(self, cmd: 'Cmd', status: str, result: Any) -> None:
        self.cmd = cmd
        self.status = status
        self.result = result

        super().__init__(
            f"Command '{cmd}' failed. Expected 'success', got '{status}'. Message: {result}"
        )

T = TypeVar('T')

@dataclass
class CmdResult(Generic[T]):
    cmd: 'Cmd'
    result: Any

    def success(self) -> T:
        status = self.result.get('status') or 'unknown'
        result = self.result.get('result') or {}

        if status == "success":
            return self.cmd.process(result)
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

    def run(self, config: str) -> CmdResult[T]:
        full_cmd = f'cargo run --bin relayer -- -c {config}'.split(' ')
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

def from_dict(klass, dikt):
    if is_dataclass(klass):
        fields = datafields(klass)
        args = { f.name: from_dict(f.type, dikt[f.name]) for f in fields }
        return klass(**args)
    else:
        return dikt

# =============================================================================

@dataclass
class Height:
    revision_height: int
    revision_number: int

@dataclass
class TxCreateClientRes:
    client_id: str

@cmd("tx raw create-client")
@dataclass
class TxCreateClient(Cmd[TxCreateClientRes]):
    dst_chain_id: str
    src_chain_id: str

    def args(self) -> List[str]:
        return [self.dst_chain_id, self.src_chain_id]

    def process(self, result: Any) -> TxCreateClientRes:
        return from_dict(TxCreateClientRes, result[0]['CreateClient'])

# -----------------------------------------------------------------------------

@dataclass
class TxUpdateClientRes:
    consensus_height: Height

@cmd("tx raw update-client")
@dataclass
class TxUpdateClient(Cmd[TxUpdateClientRes]):
    dst_chain_id: str
    src_chain_id: str
    dst_client_id: str

    def args(self) -> List[str]:
        return [self.dst_chain_id, self.src_chain_id, self.dst_client_id]

    def process(self, result: Any) -> TxUpdateClientRes:
        return from_dict(TxUpdateClientRes, result[0]['UpdateClient'])

# -----------------------------------------------------------------------------

@dataclass
class QueryClientStateRes:
    latest_height: Height

@cmd("query client state")
@dataclass
class QueryClientState(Cmd[QueryClientStateRes]):
    chain_id: str
    client_id: str
    height: Optional[int] = None
    proof: bool = False

    def args(self) -> List[str]:
        args = []

        if self.height != None: args.extend(['--height', str(self.height)])
        if self.proof: args.append('--proof')

        args.extend([self.chain_id, self.client_id])

        return args

    def process(self, result: Any) -> QueryClientStateRes:
        return from_dict(QueryClientStateRes, result[0])

# -----------------------------------------------------------------------------

def split():
    sleep(0.5)
    print()

# =============================================================================

def create_client(c, dst: str, src: str) -> TxCreateClientRes:
    cmd = TxCreateClient(dst_chain_id=dst, src_chain_id=src)
    client = cmd.run(c).success()
    l.info(f'Created client: {client.client_id}')
    return client

def update_client(c, dst: str, src: str, client_id: str) -> TxUpdateClientRes:
    cmd = TxUpdateClient(dst_chain_id=dst, src_chain_id=src, dst_client_id=client_id)
    res = cmd.run(c).success()
    l.info(f'Updated client to: {res.consensus_height}')
    return res

def query_client_state(c, chain: str, id: str) -> Any:
    cmd = QueryClientState(chain_id=chain, client_id=id)
    res = cmd.run(c).success()
    l.info(f'Client is at: {res.latest_height}')
    return res

def create_update_query_client(c, dst: str, src: str) -> str:
    client = create_client(c, dst, src)
    split()
    query_client_state(c, dst, client.client_id)
    split()
    update_client(c, dst, src, client.client_id)
    split()
    query_client_state(c, dst, client.client_id)
    split()
    return client.client_id

def main():
    l.basicConfig(
        level=l.DEBUG,
        format="[%(asctime)s] [%(levelname)8s] --- %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S"
    )

    c = 'stargate-5.toml'

    IBC_0 = 'ibc-0'
    IBC_1 = 'ibc-1'

    ibc0_client_id = create_update_query_client(c, IBC_0, IBC_1)
    ibc1_client_id = create_update_query_client(c, IBC_1, IBC_0)

    split()

if __name__ == "__main__":
    main()

