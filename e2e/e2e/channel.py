from typing import Any, List

from time import sleep
from dataclasses import dataclass

import logging as l

from .cmd import *
from .common import *


@dataclass
class TxChanOpenInitRes:
    channel_id: ChannelId
    connection_id: ConnectionId
    counterparty_channel_id: Optional[ChannelId]
    counterparty_port_id: PortId
    height: BlockHeight
    port_id: PortId


@cmd("tx raw chan-open-init")
@dataclass
class TxChanOpenInit(Cmd[TxChanOpenInitRes]):
    src_chain_id: ChainId
    dst_chain_id: ChainId
    connection_id: ConnectionId
    dst_port_id: PortId
    src_port_id: PortId
    ordering: Optional[Ordering] = None

    def args(self) -> List[str]:
        args = [self.dst_chain_id, self.src_chain_id,
                self.connection_id,
                self.dst_port_id, self.src_port_id,
                "defaultChannel", "defaultChannel"]

        if self.ordering is not None:
            args.extend(['--ordering', str(self.ordering)])

        return args

    def process(self, result: Any) -> TxChanOpenInitRes:
        return from_dict(TxChanOpenInitRes, result[0]['OpenInitChannel'])

# -----------------------------------------------------------------------------


@dataclass
class TxChanOpenTryRes:
    channel_id: ChannelId
    connection_id: ConnectionId
    counterparty_channel_id: ChannelId
    counterparty_port_id: ChannelId
    height: BlockHeight
    port_id: PortId


@cmd("tx raw chan-open-try")
@dataclass
class TxChanOpenTry(Cmd[TxChanOpenTryRes]):
    src_chain_id: ChainId
    dst_chain_id: ChainId
    connection_id: ConnectionId
    dst_port_id: PortId
    src_port_id: PortId
    src_channel_id: ChannelId
    ordering: Optional[Ordering] = None

    def args(self) -> List[str]:
        args = [self.dst_chain_id, self.src_chain_id,
                self.connection_id,
                self.dst_port_id, self.src_port_id,
                "defaultChannel", self.src_channel_id]

        if self.ordering is not None:
            args.extend(['--ordering', str(self.ordering)])

        return args

    def process(self, result: Any) -> TxChanOpenTryRes:
        return from_dict(TxChanOpenTryRes, result[0]['OpenTryChannel'])

# -----------------------------------------------------------------------------


@dataclass
class TxChanOpenAckRes:
    channel_id: ChannelId
    connection_id: ConnectionId
    counterparty_channel_id: ChannelId
    counterparty_port_id: ChannelId
    height: BlockHeight
    port_id: PortId


@cmd("tx raw chan-open-ack")
@dataclass
class TxChanOpenAck(Cmd[TxChanOpenAckRes]):
    src_chain_id: ChainId
    dst_chain_id: ChainId
    connection_id: ConnectionId
    dst_port_id: PortId
    src_port_id: PortId
    dst_channel_id: ChannelId
    src_channel_id: ChannelId

    def args(self) -> List[str]:
        args = [self.dst_chain_id, self.src_chain_id,
                self.connection_id,
                self.dst_port_id, self.src_port_id,
                self.dst_channel_id, self.src_channel_id]

        return args

    def process(self, result: Any) -> TxChanOpenAckRes:
        return from_dict(TxChanOpenAckRes, result[0]['OpenAckChannel'])

# -----------------------------------------------------------------------------


@dataclass
class TxChanOpenConfirmRes:
    channel_id: ChannelId
    connection_id: ConnectionId
    counterparty_channel_id: ChannelId
    counterparty_port_id: ChannelId
    height: BlockHeight
    port_id: PortId


@cmd("tx raw chan-open-confirm")
@dataclass
class TxChanOpenConfirm(Cmd[TxChanOpenConfirmRes]):
    src_chain_id: ChainId
    dst_chain_id: ChainId
    connection_id: ConnectionId
    dst_port_id: PortId
    src_port_id: PortId
    dst_channel_id: ChannelId
    src_channel_id: ChannelId

    def args(self) -> List[str]:
        args = [self.dst_chain_id, self.src_chain_id,
                self.connection_id,
                self.dst_port_id, self.src_port_id,
                self.dst_channel_id, self.src_channel_id]

        return args

    def process(self, result: Any) -> TxChanOpenConfirmRes:
        return from_dict(TxChanOpenConfirmRes, result[0]['OpenConfirmChannel'])

# -----------------------------------------------------------------------------


@dataclass
class Remote:
    channel_id: ChannelId
    port_id: PortId


@dataclass
class ChannelEnd:
    connection_hops: List[Any]
    ordering: str
    remote: Remote
    state: str
    version: str


@cmd("query channel end")
@dataclass
class QueryChannelEnd(Cmd[ChannelEnd]):
    chain_id: ChainId
    connection_id: ConnectionId
    channel_id: ChannelId

    def args(self) -> List[str]:
        return [self.chain_id, self.connection_id, self.channel_id]

    def process(self, result: Any) -> ChannelEnd:
        return from_dict(ChannelEnd, result[0])

# =============================================================================
# CHANNEL handshake
# =============================================================================


def chan_open_init(c: Config,
                   src: ChainId, dst: ChainId,
                   dst_conn: ConnectionId,
                   src_port: PortId = PortId('transfer'),
                   dst_port: PortId = PortId('transfer'),
                   ordering: Optional[Ordering] = None
                   ) -> ChannelId:

    cmd = TxChanOpenInit(src_chain_id=src, dst_chain_id=dst,
                         connection_id=dst_conn,
                         dst_port_id=dst_port, src_port_id=src_port,
                         ordering=ordering)

    res = cmd.run(c).success()
    l.info(
        f'ChanOpenInit submitted to {dst} and obtained channel id {res.channel_id}')
    return res.channel_id


def chan_open_try(c: Config,
                  src: ChainId, dst: ChainId,
                  dst_conn: ConnectionId,
                  src_chan: ChannelId,
                  src_port: PortId = PortId('transfer'),
                  dst_port: PortId = PortId('transfer'),
                  ordering: Optional[Ordering] = None
                  ) -> ChannelId:

    cmd = TxChanOpenTry(src_chain_id=src, dst_chain_id=dst,
                        connection_id=dst_conn,
                        dst_port_id=dst_port, src_port_id=src_port,
                        src_channel_id=src_chan,
                        ordering=ordering)

    res = cmd.run(c).success()
    l.info(
        f'ChanOpenTry submitted to {dst} and obtained channel id {res.channel_id}')
    return res.channel_id


def chan_open_ack(c: Config,
                  src: ChainId, dst: ChainId,
                  dst_conn: ConnectionId,
                  src_chan: ChannelId,
                  dst_chan: ChannelId,
                  src_port: PortId = PortId('transfer'),
                  dst_port: PortId = PortId('transfer'),
                  ) -> ChannelId:

    cmd = TxChanOpenAck(src_chain_id=src, dst_chain_id=dst,
                        connection_id=dst_conn,
                        dst_port_id=dst_port, src_port_id=src_port,
                        dst_channel_id=dst_chan,
                        src_channel_id=src_chan)

    res = cmd.run(c).success()
    l.info(
        f'ChanOpenAck submitted to {dst} and got channel id {res.channel_id}')
    return res.channel_id


def chan_open_confirm(c: Config,
                      src: ChainId, dst: ChainId,
                      dst_conn: ConnectionId,
                      src_chan: ChannelId,
                      dst_chan: ChannelId,
                      src_port: PortId = PortId('transfer'),
                      dst_port: PortId = PortId('transfer'),
                      ) -> ChannelId:

    cmd = TxChanOpenConfirm(src_chain_id=src, dst_chain_id=dst,
                            connection_id=dst_conn,
                            dst_port_id=dst_port, src_port_id=src_port,
                            dst_channel_id=dst_chan,
                            src_channel_id=src_chan)

    res = cmd.run(c).success()
    l.info(
        f'ChanOpenConfirm submitted to {dst} and got channel id {res.channel_id}')
    return res.channel_id


def handshake(c: Config,
              side_a: ChainId, side_b: ChainId,
              conn_a: ConnectionId, conn_b: ConnectionId,
              ) -> Tuple[ChannelId, ChannelId]:

    a_chan_id = chan_open_init(c, dst=side_a, src=side_b, dst_conn=conn_a)

    split()

    b_chan_id = chan_open_try(
        c, dst=side_b, src=side_a, dst_conn=conn_b, src_chan=a_chan_id)

    split()

    ack_res = chan_open_ack(c, dst=side_a, src=side_b,
                            dst_conn=conn_a, dst_chan=a_chan_id, src_chan=b_chan_id)

    if ack_res != a_chan_id:
        l.error(
            f'Incorrect channel id returned from chan open ack: expected={a_chan_id} got={ack_res}')
        exit(1)

    confirm_res = chan_open_confirm(
        c, dst=side_b, src=side_a, dst_conn=conn_b, dst_chan=b_chan_id, src_chan=a_chan_id)

    if confirm_res != b_chan_id:
        l.error(
            f'Incorrect channel id returned from chan open confirm: expected={b_chan_id} got={confirm_res}')
        exit(1)

    split()

    a_chan_end = query_channel_end(c, side_a, conn_a, a_chan_id)
    if a_chan_end.state != 'Open':
        l.warn(
            f'Channel end with id {a_chan_id} on chain {side_a} is not in Open state, got: {a_chan_end.state}')
        # exit(1)

    b_chan_end = query_channel_end(c, side_b, conn_b, a_chan_id)
    if b_chan_end.state != 'Open':
        l.warn(
            f'Channel end with id {b_chan_id} on chain {side_b} is not in Open state, got: {b_chan_end.state}')
        # exit(1)

    return a_chan_id, b_chan_id

# =============================================================================
# CHANNEL END query
# =============================================================================


def query_channel_end(c: Config, chain_id: ChainId, conn_id: ConnectionId, chan_id: ChannelId) -> ChannelEnd:
    cmd = QueryChannelEnd(chain_id, conn_id, chan_id)
    res = cmd.run(c).success()

    l.debug(f'Status of channel end {chan_id}: {res}')

    return res
