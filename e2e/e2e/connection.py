from typing import Tuple

from .cmd import *
from .common import *


@dataclass
class TxConnInitRes:
    connection_id: ConnectionId


@cmd("tx raw conn-init")
@dataclass
class TxConnInit(Cmd[TxConnInitRes]):
    dst_chain_id: ChainId
    src_chain_id: ChainId
    dst_client_id: ClientId
    src_client_id: ClientId

    def args(self) -> List[str]:
        return [self.dst_chain_id, self.src_chain_id,
                self.dst_client_id, self.src_client_id]

    def process(self, result: Any) -> TxConnInitRes:
        return from_dict(TxConnInitRes, result[0]['OpenInitConnection'])


# -----------------------------------------------------------------------------

@dataclass
class TxConnTryRes:
    connection_id: ConnectionId


@cmd("tx raw conn-try")
@dataclass
class TxConnTry(Cmd[TxConnTryRes]):
    dst_chain_id: ChainId
    src_chain_id: ChainId
    dst_client_id: ClientId
    src_client_id: ClientId
    src_conn_id: ConnectionId

    def args(self) -> List[str]:
        return [self.dst_chain_id, self.src_chain_id,
                self.dst_client_id, self.src_client_id,
                "-s", self.src_conn_id]

    def process(self, result: Any) -> TxConnTryRes:
        return from_dict(TxConnTryRes, result[0]['OpenTryConnection'])


# -----------------------------------------------------------------------------

@dataclass
class TxConnAckRes:
    connection_id: ConnectionId


@cmd("tx raw conn-ack")
@dataclass
class TxConnAck(Cmd[TxConnAckRes]):
    dst_chain_id: ChainId
    src_chain_id: ChainId
    dst_client_id: ClientId
    src_client_id: ClientId
    dst_conn_id: ConnectionId
    src_conn_id: ConnectionId

    def args(self) -> List[str]:
        return [self.dst_chain_id, self.src_chain_id,
                self.dst_client_id, self.src_client_id,
                "-d", self.dst_conn_id,
                "-s", self.src_conn_id]

    def process(self, result: Any) -> TxConnAckRes:
        return from_dict(TxConnAckRes, result[0]['OpenAckConnection'])


# -----------------------------------------------------------------------------

@dataclass
class TxConnConfirmRes:
    connection_id: ConnectionId


@cmd("tx raw conn-confirm")
@dataclass
class TxConnConfirm(Cmd[TxConnConfirmRes]):
    dst_chain_id: ChainId
    src_chain_id: ChainId
    dst_client_id: ClientId
    src_client_id: ClientId
    dst_conn_id: ConnectionId
    src_conn_id: ConnectionId

    def args(self) -> List[str]:
        return [self.dst_chain_id, self.src_chain_id,
                self.dst_client_id, self.src_client_id,
                "-d", self.dst_conn_id,
                "-s", self.src_conn_id]

    def process(self, result: Any) -> TxConnConfirmRes:
        return from_dict(TxConnConfirmRes, result[0]['OpenConfirmConnection'])


# -----------------------------------------------------------------------------

@dataclass
class Version:
    features: List[str]
    identifier: str


@dataclass
class Counterparty:
    client_id: ClientId
    connection_id: ConnectionId
    prefix: str


@dataclass
class ConnectionEnd:
    client_id: ClientId
    counterparty: Counterparty
    delay_period: int
    state: str
    versions: List[Version]


@cmd("query connection end")
@dataclass
class QueryConnectionEnd(Cmd[ConnectionEnd]):
    chain_id: ChainId
    connection_id: ConnectionId

    def args(self) -> List[str]:
        return [self.chain_id, self.connection_id]

    def process(self, result: Any) -> ConnectionEnd:
        return from_dict(ConnectionEnd, result[0])


# =============================================================================
# CONNECTION handshake
# =============================================================================


def conn_init(c: Config,
              dst: ChainId, src: ChainId,
              dst_client: ClientId, src_client: ClientId
              ) -> ConnectionId:
    cmd = TxConnInit(dst_chain_id=dst, src_chain_id=src,
                     dst_client_id=dst_client, src_client_id=src_client)
    res = cmd.run(c).success()
    l.info(
        f'ConnOpen init submitted to {dst} and obtained connection id {res.connection_id}')
    return res.connection_id


def conn_try(c: Config,
             dst: ChainId, src: ChainId,
             dst_client: ClientId, src_client: ClientId,
             src_conn: ConnectionId
             ) -> ConnectionId:
    cmd = TxConnTry(dst_chain_id=dst, src_chain_id=src, dst_client_id=dst_client, src_client_id=src_client,
                    src_conn_id=src_conn)
    res = cmd.run(c).success()
    l.info(
        f'ConnOpen try submitted to {dst} and obtained connection id {res.connection_id}')
    return res.connection_id


def conn_ack(c: Config,
             dst: ChainId, src: ChainId,
             dst_client: ClientId, src_client: ClientId,
             dst_conn: ConnectionId, src_conn: ConnectionId
             ) -> ConnectionId:
    cmd = TxConnAck(dst_chain_id=dst, src_chain_id=src, dst_client_id=dst_client, src_client_id=src_client,
                    dst_conn_id=dst_conn, src_conn_id=src_conn)
    res = cmd.run(c).success()
    l.info(
        f'ConnOpen ack submitted to {dst} and obtained connection id {res.connection_id}')
    return res.connection_id


def conn_confirm(c: Config,
                 dst: ChainId, src: ChainId,
                 dst_client: ClientId, src_client: ClientId,
                 dst_conn: ConnectionId, src_conn: ConnectionId
                 ) -> ConnectionId:
    cmd = TxConnConfirm(dst_chain_id=dst, src_chain_id=src, dst_client_id=dst_client, src_client_id=src_client,
                        dst_conn_id=dst_conn, src_conn_id=src_conn)
    res = cmd.run(c).success()
    l.info(
        f'ConnOpen confirm submitted to {dst} and obtained connection id {res.connection_id}')
    return res.connection_id


def handshake(c: Config,
              side_a: ChainId, side_b: ChainId,
              client_a: ClientId, client_b: ClientId
              ) -> Tuple[ConnectionId, ConnectionId]:
    a_conn_id = conn_init(c, side_a, side_b, client_a, client_b)
    split()
    b_conn_id = conn_try(c, side_b, side_a, client_b, client_a, a_conn_id)
    split()
    ack_res = conn_ack(
        c, side_a, side_b, client_a, client_b, a_conn_id, b_conn_id)

    if ack_res != a_conn_id:
        l.error(
            f'Incorrect connection id returned from conn ack: expected=({a_conn_id})/got=({ack_res})')
        exit(1)

    split()

    confirm_res = conn_confirm(
        c, side_b, side_a, client_b, client_a, b_conn_id, a_conn_id)

    if confirm_res != b_conn_id:
        l.error(
            f'Incorrect connection id returned from conn confirm: expected=({b_conn_id})/got=({confirm_res})')
        exit(1)

    a_conn_end = query_connection_end(c, side_a, a_conn_id)
    if a_conn_end.state != 'Open':
        l.error(
            f'Connection end with id {a_conn_id} is not in Open state, got: {a_conn_end.state}')
        exit(1)

    b_conn_end = query_connection_end(c, side_b, b_conn_id)
    if b_conn_end.state != 'Open':
        l.error(
            f'Connection end with id {b_conn_id} is not in Open state, got: {b_conn_end.state}')
        exit(1)

    return a_conn_id, b_conn_id


# =============================================================================
# CONNECTION END query
# =============================================================================


def query_connection_end(c: Config, chain_id: ChainId, conn_id: ConnectionId) -> ConnectionEnd:
    cmd = QueryConnectionEnd(chain_id, conn_id)
    res = cmd.run(c).success()

    l.debug(f'Status of connection end {conn_id}: {res}')

    return res
