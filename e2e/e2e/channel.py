from typing import Optional, Tuple
import toml

from .cmd import *
from .common import *

import e2e.relayer as relayer

@dataclass
class TxChanOpenInitRes:
    channel_id: ChannelId
    connection_id: ConnectionId
    counterparty_channel_id: Optional[ChannelId]
    counterparty_port_id: PortId
    port_id: PortId


@cmd("tx chan-open-init")
@dataclass
class TxChanOpenInit(Cmd[TxChanOpenInitRes]):
    dst_chain_id: ChainId
    src_chain_id: ChainId
    connection_id: ConnectionId
    dst_port_id: PortId
    src_port_id: PortId
    ordering: Optional[Ordering] = None

    def args(self) -> List[str]:
        args = ["--dst-chain", self.dst_chain_id, "--src-chain", self.src_chain_id,
                "--dst-connection", self.connection_id,
                "--dst-port", self.dst_port_id, "--src-port", self.src_port_id]

        if self.ordering is not None:
            args.extend(['--ordering', str(self.ordering)])

        return args

    def process(self, result: Any) -> TxChanOpenInitRes:
        return from_dict(TxChanOpenInitRes, result['OpenInitChannel'])


# -----------------------------------------------------------------------------


@dataclass
class TxChanOpenTryRes:
    channel_id: ChannelId
    connection_id: ConnectionId
    counterparty_channel_id: ChannelId
    counterparty_port_id: ChannelId
    port_id: PortId


@cmd("tx chan-open-try")
@dataclass
class TxChanOpenTry(Cmd[TxChanOpenTryRes]):
    dst_chain_id: ChainId
    src_chain_id: ChainId
    connection_id: ConnectionId
    dst_port_id: PortId
    src_port_id: PortId
    src_channel_id: ChannelId
    ordering: Optional[Ordering] = None

    def args(self) -> List[str]:
        args = ["--dst-chain", self.dst_chain_id, "--src-chain", self.src_chain_id,
                "--dst-connection", self.connection_id,
                "--dst-port", self.dst_port_id, "--src-port", self.src_port_id,
                "--src-channel", self.src_channel_id]

        if self.ordering is not None:
            args.extend(['--ordering', str(self.ordering)])

        return args

    def process(self, result: Any) -> TxChanOpenTryRes:
        return from_dict(TxChanOpenTryRes, result['OpenTryChannel'])


# -----------------------------------------------------------------------------


@dataclass
class TxChanOpenAckRes:
    channel_id: ChannelId
    connection_id: ConnectionId
    counterparty_channel_id: ChannelId
    counterparty_port_id: ChannelId
    port_id: PortId


@cmd("tx chan-open-ack")
@dataclass
class TxChanOpenAck(Cmd[TxChanOpenAckRes]):
    dst_chain_id: ChainId
    src_chain_id: ChainId
    connection_id: ConnectionId
    dst_port_id: PortId
    src_port_id: PortId
    dst_channel_id: ChannelId
    src_channel_id: ChannelId

    def args(self) -> List[str]:
        args = ["--dst-chain", self.dst_chain_id, "--src-chain", self.src_chain_id,
                "--dst-connection", self.connection_id,
                "--dst-port", self.dst_port_id, "--src-port", self.src_port_id,
                "--dst-channel", self.dst_channel_id,
                "--src-channel", self.src_channel_id]

        return args

    def process(self, result: Any) -> TxChanOpenAckRes:
        return from_dict(TxChanOpenAckRes, result['OpenAckChannel'])


# -----------------------------------------------------------------------------


@dataclass
class TxChanOpenConfirmRes:
    channel_id: ChannelId
    connection_id: ConnectionId
    counterparty_channel_id: ChannelId
    counterparty_port_id: ChannelId
    port_id: PortId


@cmd("tx chan-open-confirm")
@dataclass
class TxChanOpenConfirm(Cmd[TxChanOpenConfirmRes]):
    dst_chain_id: ChainId
    src_chain_id: ChainId
    connection_id: ConnectionId
    dst_port_id: PortId
    src_port_id: PortId
    dst_channel_id: ChannelId
    src_channel_id: ChannelId

    def args(self) -> List[str]:
        args = ["--dst-chain", self.dst_chain_id, "--src-chain", self.src_chain_id,
                "--dst-connection", self.connection_id,
                "--dst-port", self.dst_port_id, "--src-port", self.src_port_id,
                "--dst-channel", self.dst_channel_id,
                "--src-channel", self.src_channel_id]

        return args

    def process(self, result: Any) -> TxChanOpenConfirmRes:
        return from_dict(TxChanOpenConfirmRes, result['OpenConfirmChannel'])

# -----------------------------------------------------------------------------


@dataclass
class TxChanCloseInitRes:
    channel_id: ChannelId
    connection_id: ConnectionId
    counterparty_channel_id: ChannelId
    counterparty_port_id: ChannelId
    port_id: PortId


@cmd("tx chan-close-init")
@dataclass
class TxChanCloseInit(Cmd[TxChanCloseInitRes]):
    dst_chain_id: ChainId
    src_chain_id: ChainId
    dst_conn_id: ConnectionId
    dst_port_id: PortId
    src_port_id: PortId
    dst_chan_id: ChannelId
    src_chan_id: ChannelId

    def args(self) -> List[str]:
        args = ["--dst-chain", self.dst_chain_id, "--src-chain", self.src_chain_id,
                "--dst-connection", self.dst_conn_id,
                "--dst-port", self.dst_port_id, "--src-port", self.src_port_id,
                "--dst-channel", self.dst_chan_id,
                "--src-channel", self.src_chan_id]

        return args

    def process(self, result: Any) -> TxChanCloseInitRes:
        print(result)
        return from_dict(TxChanCloseConfirmRes, result['CloseInitChannel'])

# -----------------------------------------------------------------------------


@dataclass
class TxChanCloseConfirmRes:
    channel_id: ChannelId
    connection_id: ConnectionId
    counterparty_channel_id: ChannelId
    counterparty_port_id: ChannelId
    port_id: PortId


@cmd("tx chan-close-confirm")
@dataclass
class TxChanCloseConfirm(Cmd[TxChanCloseConfirmRes]):
    dst_chain_id: ChainId
    src_chain_id: ChainId
    dst_conn_id: ConnectionId
    dst_port_id: PortId
    src_port_id: PortId
    dst_chan_id: ChannelId
    src_chan_id: ChannelId

    def args(self) -> List[str]:
        args = ["--dst-chain", self.dst_chain_id, "--src-chain", self.src_chain_id,
                "--dst-connection", self.dst_conn_id,
                "--dst-port", self.dst_port_id, "--src-port", self.src_port_id,
                "--dst-channel", self.dst_chan_id,
                "--src-channel", self.src_chan_id]

        return args

    def process(self, result: Any) -> TxChanCloseConfirmRes:
        print(result)
        return from_dict(TxChanCloseConfirmRes, result['CloseConfirmChannel'])


# -----------------------------------------------------------------------------


@ dataclass
class Remote:
    channel_id: ChannelId
    port_id: PortId


@ dataclass
class ChannelEnd:
    connection_hops: List[Any]
    ordering: str
    remote: Remote
    state: str
    version: str

@ dataclass
class ChannelEnds:
    chain_id: str
    client_id: str
    connection_id: str
    channel_id: str
    port_id: str

    counterparty_chain_id: str
    counterparty_client_id: str
    counterparty_connection_id: str
    counterparty_channel_id: str
    counterparty_port_id: str


@ cmd("query channel end")
@ dataclass
class QueryChannelEnd(Cmd[ChannelEnd]):
    chain_id: ChainId
    port_id: PortId
    channel_id: ChannelId

    def args(self) -> List[str]:
        return ["--chain", self.chain_id, "--port", self.port_id, "--chan", self.channel_id]

    def process(self, result: Any) -> ChannelEnd:
        return from_dict(ChannelEnd, result)

@ cmd("query channel ends")
@ dataclass
class QueryChannelEnds(Cmd[ChannelEnds]):
    chain_id: ChainId
    port_id: PortId
    channel_id: ChannelId

    def args(self) -> List[str]:
        return ["--chain", self.chain_id, "--port", self.port_id, "--chan", self.channel_id]

    def process(self, result: Any) -> ChannelEnds:
        return from_dict(ChannelEnds, result)

# =============================================================================
# CHANNEL handshake
# =============================================================================


def chan_open_init(c: Config,
                   dst: ChainId, src: ChainId,
                   dst_conn: ConnectionId,
                   dst_port: PortId = PortId('transfer'),
                   src_port: PortId = PortId('transfer'),
                   ordering: Optional[Ordering] = None
                   ) -> ChannelId:
    cmd = TxChanOpenInit(dst_chain_id=dst, src_chain_id=src,
                         connection_id=dst_conn,
                         dst_port_id=dst_port, src_port_id=src_port,
                         ordering=ordering)

    res = cmd.run(c).success()
    l.info(
        f'ChanOpenInit submitted to {dst} and obtained channel id {res.channel_id}')
    return res.channel_id


def chan_open_try(c: Config,
                  dst: ChainId,
                  src: ChainId,
                  dst_conn: ConnectionId,
                  dst_port: PortId,
                  src_port: PortId,
                  src_chan: ChannelId,
                  ordering: Optional[Ordering] = None
                  ) -> ChannelId:
    cmd = TxChanOpenTry(dst_chain_id=dst, src_chain_id=src,
                        connection_id=dst_conn,
                        dst_port_id=dst_port, src_port_id=src_port,
                        src_channel_id=src_chan,
                        ordering=ordering)

    res = cmd.run(c).success()
    l.info(
        f'ChanOpenTry submitted to {dst} and obtained channel id {res.channel_id}')
    return res.channel_id


def chan_open_ack(c: Config,
                  dst: ChainId, src: ChainId,
                  dst_conn: ConnectionId,
                  dst_port: PortId,
                  src_port: PortId,
                  dst_chan: ChannelId,
                  src_chan: ChannelId,
                  ) -> ChannelId:
    cmd = TxChanOpenAck(dst_chain_id=dst, src_chain_id=src,
                        connection_id=dst_conn,
                        dst_port_id=dst_port, src_port_id=src_port,
                        dst_channel_id=dst_chan,
                        src_channel_id=src_chan)

    res = cmd.run(c).success()
    l.info(
        f'ChanOpenAck submitted to {dst} and got channel id {res.channel_id}')
    return res.channel_id


def chan_open_confirm(
        c: Config,
        dst: ChainId,
        src: ChainId,
        dst_conn: ConnectionId,
        dst_port: PortId,
        src_port: PortId,
        dst_chan: ChannelId,
        src_chan: ChannelId
) -> ChannelId:
    cmd = TxChanOpenConfirm(dst_chain_id=dst, src_chain_id=src,
                            connection_id=dst_conn,
                            dst_port_id=dst_port, src_port_id=src_port,
                            dst_channel_id=dst_chan,
                            src_channel_id=src_chan)

    res = cmd.run(c).success()
    l.info(
        f'ChanOpenConfirm submitted to {dst} and got channel id {res.channel_id}')
    return res.channel_id

# =============================================================================
# CHANNEL close
# =============================================================================


def chan_close_init(
        c: Config,
        dst: ChainId,
        src: ChainId,
        dst_conn: ConnectionId,
        dst_port: PortId,
        src_port: PortId,
        dst_chan: ChannelId,
        src_chan: ChannelId
) -> ChannelId:
    cmd = TxChanCloseInit(dst_chain_id=dst, src_chain_id=src,
                          dst_conn_id=dst_conn,
                          dst_port_id=dst_port, src_port_id=src_port,
                          dst_chan_id=dst_chan,
                          src_chan_id=src_chan)

    res = cmd.run(c).success()
    l.info(
        f'ChannelCloseInit submitted to {dst} and got channel id {res.channel_id}')
    return res.channel_id


def chan_close_confirm(
        c: Config,
        dst: ChainId,
        src: ChainId,
        dst_conn: ConnectionId,
        dst_port: PortId,
        src_port: PortId,
        dst_chan: ChannelId,
        src_chan: ChannelId
) -> ChannelId:
    cmd = TxChanCloseConfirm(dst_chain_id=dst, src_chain_id=src,
                             dst_conn_id=dst_conn,
                             dst_port_id=dst_port, src_port_id=src_port,
                             dst_chan_id=dst_chan,
                             src_chan_id=src_chan)

    res = cmd.run(c).success()
    l.info(
        f'ChannelCloseConfirm submitted to {dst} and got channel id {res.channel_id}')
    return res.channel_id


def close(
        c: Config,
        dst: ChainId,
        src: ChainId,
        dst_conn: ConnectionId,
        src_conn: ConnectionId,
        dst_chan: ChannelId,
        src_chan: ChannelId,
        dst_port: PortId = PortId('transfer'),
        src_port: PortId = PortId('transfer'),
):
    chan_close_init(c, dst, src, dst_conn, dst_port,
                    src_port, dst_chan, src_chan)

    chan_close_confirm(c, src, dst, src_conn, src_port,
                       dst_port, src_chan, dst_chan)


# =============================================================================
# CHANNEL handshake
# =============================================================================


def handshake(
    c: Config,
    side_a: ChainId, side_b: ChainId,
    conn_a: ConnectionId, conn_b: ConnectionId,
    port_id: PortId
) -> Tuple[ChannelId, ChannelId]:
    a_chan_id = chan_open_init(c, dst=side_a, src=side_b, dst_conn=conn_a)

    split()

    b_chan_id = chan_open_try(
        c, dst=side_b, src=side_a, dst_conn=conn_b, dst_port=port_id, src_port=port_id,
        src_chan=a_chan_id)

    split()

    ack_res = chan_open_ack(c, dst=side_a, src=side_b, dst_port=port_id, src_port=port_id,
                            dst_conn=conn_a, dst_chan=a_chan_id, src_chan=b_chan_id)

    if ack_res != a_chan_id:
        l.error(
            f'Incorrect channel id returned from chan open ack: expected={a_chan_id} got={ack_res}')
        exit(1)

    confirm_res = chan_open_confirm(
        c, dst=side_b, src=side_a, dst_port=port_id, src_port=port_id,
        dst_conn=conn_b, dst_chan=b_chan_id, src_chan=a_chan_id)

    if confirm_res != b_chan_id:
        l.error(
            f'Incorrect channel id returned from chan open confirm: expected={b_chan_id} got={confirm_res}')
        exit(1)

    split()

    a_chan_end = query_channel_end(c, side_a, port_id, a_chan_id)
    if a_chan_end.state != 'Open':
        l.error(
            f'Channel end with id {a_chan_id} on chain {side_a} is not in Open state, got: {a_chan_end.state}')
        exit(1)

    b_chan_end = query_channel_end(c, side_b, port_id, b_chan_id)
    if b_chan_end.state != 'Open':
        l.error(
            f'Channel end with id {b_chan_id} on chain {side_b} is not in Open state, got: {b_chan_end.state}')
        exit(1)

    a_chan_ends = query_channel_ends(c, side_a, port_id, a_chan_id)
    l.debug(f'query channel ends result: {a_chan_ends}')

    assert a_chan_ends.chain_id == side_a
    assert a_chan_ends.connection_id == conn_a
    assert a_chan_ends.port_id == port_id
    assert a_chan_ends.channel_id == a_chan_id

    assert a_chan_ends.counterparty_chain_id == side_b
    assert a_chan_ends.counterparty_connection_id == conn_b
    assert a_chan_ends.counterparty_port_id == port_id
    assert a_chan_ends.counterparty_channel_id == b_chan_id

    b_chan_ends = query_channel_ends(c, side_b, port_id, b_chan_id)
    l.debug(f'query channel ends result: {b_chan_ends}')

    assert b_chan_ends.chain_id == side_b
    assert b_chan_ends.connection_id == conn_b
    assert b_chan_ends.port_id == port_id
    assert b_chan_ends.channel_id == b_chan_id

    assert b_chan_ends.counterparty_chain_id == side_a
    assert b_chan_ends.counterparty_connection_id == conn_a
    assert b_chan_ends.counterparty_port_id == port_id
    assert b_chan_ends.counterparty_channel_id == a_chan_id

    return a_chan_id, b_chan_id


# =============================================================================
# CHANNEL END query
# =============================================================================


def query_channel_end(c: Config, chain_id: ChainId, port: PortId, chan_id: ChannelId) -> ChannelEnd:
    cmd = QueryChannelEnd(chain_id, port, chan_id)
    res = cmd.run(c).success()

    l.debug(f'Status of channel end {chan_id}: {res}')

    return res


# =============================================================================
# CHANNEL ENDS query
# =============================================================================

def query_channel_ends(c: Config, chain_id: ChainId, port: PortId, chan_id: ChannelId) -> ChannelEnd:
    cmd = QueryChannelEnds(chain_id, port, chan_id)
    res = cmd.run(c).success()

    l.debug(f'Status of channel ends {chan_id}: {res}')

    return res


# =============================================================================
# Passive CHANNEL relayer tests
# =============================================================================

def verify_state(c: Config,
    ibc1: ChainId, ibc0: ChainId,
    ibc1_chan_id: ChannelId, port_id: PortId):

    mode = toml.load(c.config_file)['mode']
    chan_enabled = mode['channels']['enabled']

    # verify channel state on both chains, should be 'Open' or 'Init' depending on config 'mode'
    if chan_enabled:
        sleep(10.0)
        for i in range(20):
            sleep(2.0)
            ibc1_chan_end = query_channel_end(c, ibc1, port_id, ibc1_chan_id)
            ibc0_chan_id = ibc1_chan_end.remote.channel_id
            ibc0_chan_end = query_channel_end(c, ibc0, port_id, ibc0_chan_id)
            if ibc0_chan_end.state == 'Open' and ibc1_chan_end.state == 'Open':
                break
        else:
            assert (ibc0_chan_end.state == 'Open'), (ibc0_chan_end, "state is not Open")
            assert (ibc1_chan_end.state == 'Open'), (ibc1_chan_end, "state is not Open")

    else:
        sleep(5.0)
        ibc1_chan_end = query_channel_end(c, ibc1, port_id, ibc1_chan_id)
        assert (ibc1_chan_end.state == 'Init'), (ibc1_chan_end, "state is not Init")


def passive_channel_start_then_init(c: Config,
    ibc1: ChainId, ibc0: ChainId,
    ibc1_conn_id: ConnectionId, port_id: PortId):

    # 1. start hermes
    proc = relayer.start(c)
    sleep(2.0)

    # 2. create a channel in Init state
    ibc1_chan_id = chan_open_init(c, dst=ibc1, src=ibc0, dst_conn=ibc1_conn_id)

    # 3. wait for channel handshake to finish and verify channel state on both chains
    verify_state(c, ibc1, ibc0, ibc1_chan_id, port_id)

    # 4. All good, stop the relayer
    proc.kill()


def passive_channel_init_then_start(c: Config,
    ibc1: ChainId, ibc0: ChainId,
    ibc1_conn_id: ConnectionId, port_id: PortId):

    # 1. create a channel in Init state
    ibc1_chan_id = chan_open_init(c, dst=ibc1, src=ibc0, dst_conn=ibc1_conn_id)
    sleep(2.0)

    # 2. start relaying
    proc = relayer.start(c)

    # 3. wait for channel handshake to finish and verify channel state on both chains
    verify_state(c, ibc1, ibc0, ibc1_chan_id, port_id)

    # 4. All good, stop the relayer
    proc.kill()


def passive_channel_try_then_start(c: Config,
    ibc1: ChainId,
    ibc0: ChainId,
    ibc1_conn_id: ConnectionId,
    ibc0_conn_id: ConnectionId,
    port_id: PortId):

    # 1. create a channel in Try state
    ibc1_chan_id = chan_open_init(c, dst=ibc1, src=ibc0, dst_conn=ibc1_conn_id)
    sleep(2.0)
    ibc0_chan_id = chan_open_try(c, dst=ibc0, src=ibc1, dst_conn=ibc0_conn_id, src_port=port_id, dst_port=port_id, src_chan=ibc1_chan_id)
    sleep(2.0)

    # 2. start relaying
    proc = relayer.start(c)

    # 3. wait for channel handshake to finish and verify channel state on both chains
    verify_state(c, ibc1, ibc0, ibc1_chan_id, port_id)

    # 4. All good, stop the relayer
    proc.kill()
