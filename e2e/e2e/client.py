from typing import Any, List

from time import sleep
from dataclasses import dataclass

import logging as l

from .cmd import *
from .common import *


@dataclass
class ClientCreated:
    client_id: ClientId
    client_type: ClientType
    consensus_height: Height
    height: BlockHeight


@dataclass
@cmd("tx raw create-client")
class TxCreateClient(Cmd[ClientCreated]):
    dst_chain_id: ChainId
    src_chain_id: ChainId

    def args(self) -> List[str]:
        return [self.dst_chain_id, self.src_chain_id]

    def process(self, result: Any) -> ClientCreated:
        return from_dict(ClientCreated, result[0]['CreateClient'])


# -----------------------------------------------------------------------------


@dataclass
class ClientUpdated:
    client_id: ClientId
    client_type: ClientType
    consensus_height: Height
    height: BlockHeight


@dataclass
@cmd("tx raw update-client")
class TxUpdateClient(Cmd[ClientUpdated]):
    dst_chain_id: ChainId
    src_chain_id: ChainId
    dst_client_id: ClientId

    def args(self) -> List[str]:
        return [self.dst_chain_id, self.src_chain_id, self.dst_client_id]

    def process(self, result: Any) -> ClientUpdated:
        return from_dict(ClientUpdated, result[0]['UpdateClient'])


# -----------------------------------------------------------------------------


@dataclass
class ClientState:
    allow_update_after_expiry: bool
    allow_update_after_misbehaviour: bool
    chain_id: ChainId
    frozen_height: Height
    latest_height: Height
    max_clock_drift: Duration
    trust_level: TrustLevel
    trusting_period: Duration
    unbonding_period: Duration
    upgrade_path: List[str]


@dataclass
@cmd("query client state")
class QueryClientState(Cmd[ClientState]):
    chain_id: ChainId
    client_id: ClientId
    height: Optional[int] = None
    proof: bool = False

    def args(self) -> List[str]:
        args = []

        if self.height is not None:
            args.extend(['--height', str(self.height)])
        if self.proof:
            args.append('--proof')

        args.extend([self.chain_id, self.client_id])

        return args

    def process(self, result: Any) -> ClientState:
        return from_dict(ClientState, result[0])

# =============================================================================
# CLIENT creation and manipulation
# =============================================================================


def create_client(c: Config, dst: ChainId, src: ChainId) -> ClientCreated:
    cmd = TxCreateClient(dst_chain_id=dst, src_chain_id=src)
    client = cmd.run(c).success()
    l.info(f'Created client: {client.client_id}')
    return client


def update_client(c: Config, dst: ChainId, src: ChainId, client_id: ClientId) -> ClientUpdated:
    cmd = TxUpdateClient(dst_chain_id=dst, src_chain_id=src,
                         dst_client_id=client_id)
    res = cmd.run(c).success()
    l.info(f'Updated client to: {res.consensus_height}')
    return res


def query_client_state(c: Config, chain_id: ChainId, client_id: ClientId) -> Tuple[ClientId, ClientState]:
    cmd = QueryClientState(chain_id, client_id)
    res = cmd.run(c).success()
    l.debug(f'State of client {client_id} is: {res}')
    return client_id, res


def create_update_query_client(c: Config, dst: ChainId, src: ChainId) -> ClientId:
    client = create_client(c, dst, src)
    split()
    query_client_state(c, dst, client.client_id)
    split()
    update_client(c, dst, src, client.client_id)
    split()
    query_client_state(c, dst, client.client_id)
    split()
    return client.client_id
