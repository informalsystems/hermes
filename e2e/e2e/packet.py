from typing import Optional

from .cmd import *
from .common import *


@dataclass
class Packet:
    sequence: Sequence
    source_port: PortId
    source_channel: ChannelId
    destination_port: PortId
    destination_channel: ChannelId
    data: Hex
    timeout_height: TimeoutHeight
    timeout_timestamp: Timestamp


@dataclass
class TxPacketSendRes:
    packet: Packet


@cmd("tx ft-transfer")
@dataclass
class TxPacketSend(Cmd[TxPacketSendRes]):
    dst_chain_id: ChainId
    src_chain_id: ChainId
    src_port: PortId
    src_channel: ChannelId
    amount: int
    height_offset: int
    number_msgs: Optional[int] = None
    key: Optional[str] = None

    def args(self) -> List[str]:
        args = [
            "--dst-chain", self.dst_chain_id,
            "--src-chain", self.src_chain_id,
            "--src-port", self.src_port,
            "--src-channel", self.src_channel,
            "--amount", str(self.amount),
            "--timeout-height-offset", str(self.height_offset),
        ]

        if self.number_msgs != None:
            args.extend(['--number-msgs', str(self.number_msgs)])

        if self.key != None:
            args.extend(['--key-name', str(self.key)])

        return args

    def process(self, result: Any) -> TxPacketSendRes:
        entry = find_entry(result, 'event')
        return from_dict(TxPacketSendRes, entry['SendPacket'])

# -----------------------------------------------------------------------------


@dataclass
class TxPacketRecvRes:
    packet: Packet
    ack: Hex


@cmd("tx packet-recv")
@dataclass
class TxPacketRecv(Cmd[TxPacketRecvRes]):
    dst_chain_id: ChainId
    src_chain_id: ChainId
    src_port: PortId
    src_channel: ChannelId

    def args(self) -> List[str]:
        return ["--dst-chain", self.dst_chain_id, "--src-chain", self.src_chain_id, "--src-port", self.src_port, "--src-channel", self.src_channel]

    def process(self, result: Any) -> TxPacketRecvRes:
        entry = find_entry(result, 'WriteAcknowledgement')
        return from_dict(TxPacketRecvRes, entry)

# -----------------------------------------------------------------------------


@dataclass
class TxPacketTimeoutRes:
    packet: Packet


@cmd("tx packet-recv")
@dataclass
class TxPacketTimeout(Cmd[TxPacketTimeoutRes]):
    dst_chain_id: ChainId
    src_chain_id: ChainId
    src_port: PortId
    src_channel: ChannelId

    def args(self) -> List[str]:
        return ["--dst-chain", self.dst_chain_id, "--src-chain", self.src_chain_id, "--src-port", self.src_port, "--src-channel", self.src_channel]

    def process(self, result: Any) -> TxPacketTimeoutRes:
        entry = find_entry(result, 'TimeoutPacket')
        return from_dict(TxPacketTimeoutRes, entry)


# -----------------------------------------------------------------------------


@dataclass
class TxPacketAckRes:
    packet: Packet


@cmd("tx packet-ack")
@dataclass
class TxPacketAck(Cmd[TxPacketAckRes]):
    dst_chain_id: ChainId
    src_chain_id: ChainId
    src_port: PortId
    src_channel: ChannelId

    def args(self) -> List[str]:
        return ["--dst-chain", self.dst_chain_id, "--src-chain", self.src_chain_id, "--src-port", self.src_port, "--src-channel", self.src_channel]

    def process(self, result: Any) -> TxPacketAckRes:
        entry = find_entry(result, 'AcknowledgePacket')
        return from_dict(TxPacketAckRes, entry)


# -----------------------------------------------------------------------------

@cmd("query packet pending-sends")
@dataclass
class QueryUnreceivedPackets(Cmd[List[int]]):
    chain: ChainId
    port: PortId
    channel: ChannelId

    def args(self) -> List[str]:
        return ["--chain", self.chain, "--port", self.port, "--chan", self.channel]

    def process(self, result: Any) -> List[int]:
        return from_dict(List[int], result)


def query_unreceived_packets(
    c: Config,
    chain: ChainId,
    port: PortId,
    channel: ChannelId,
) -> List[int]:
    cmd = QueryUnreceivedPackets(
        chain=chain, port=port, channel=channel)

    return cmd.run(c).success()

# -----------------------------------------------------------------------------


@cmd("query packet pending-acks")
@dataclass
class QueryUnreceivedAcks(Cmd[List[int]]):
    chain: ChainId
    port: PortId
    channel: ChannelId

    def args(self) -> List[str]:
        return ["--chain", self.chain, "--port", self.port, "--chan", self.channel]

    def process(self, result: Any) -> List[int]:
        return from_dict(List[int], result)


def query_unreceived_acks(
    c: Config,
    chain: ChainId,
    port: PortId,
    channel: ChannelId,
) -> List[int]:
    cmd = QueryUnreceivedAcks(
        chain=chain, port=port, channel=channel)

    return cmd.run(c).success()


# TRANSFER (packet send)
# =============================================================================


def packet_send(c: Config, src: ChainId, dst: ChainId,
                src_port: PortId, src_channel: ChannelId,
                amount: int, height_offset: int, number_msgs: Optional[int] = None,
                key: Optional[str] = 'user2') -> Packet:

    cmd = TxPacketSend(dst_chain_id=dst, src_chain_id=src,
                       src_port=src_port, src_channel=src_channel,
                       amount=amount,
                       number_msgs=number_msgs,
                       height_offset=height_offset,
                       key=key)

    res = cmd.run(c).success()
    l.info(
        f'PacketSend to {src} and obtained sequence number {res.packet.sequence}')

    return res.packet


def packet_recv(c: Config, dst: ChainId, src: ChainId, src_port: PortId, src_channel: ChannelId) -> Packet:
    cmd = TxPacketRecv(dst_chain_id=dst, src_chain_id=src,
                       src_port=src_port, src_channel=src_channel)

    res = cmd.run(c).success()
    l.info(
        f'PacketRecv to {dst} done for sequence number {res.packet.sequence}')

    return res.packet


def packet_timeout(c: Config, dst: ChainId, src: ChainId, src_port: PortId, src_channel: ChannelId) -> Packet:
    cmd = TxPacketTimeout(dst_chain_id=dst, src_chain_id=src,
                          src_port=src_port, src_channel=src_channel)

    res = cmd.run(c).success()
    l.info(
        f'Timeout to {src} done for sequence number {res.packet.sequence}')

    return res.packet


def packet_ack(c: Config, dst: ChainId, src: ChainId, src_port: PortId, src_channel: ChannelId) -> Packet:
    cmd = TxPacketAck(dst_chain_id=dst, src_chain_id=src,
                      src_port=src_port, src_channel=src_channel)

    res = cmd.run(c).success()
    l.info(
        f'PacketAck to {dst} done for sequence number {res.packet.sequence}')

    return res.packet


def ping_pong(c: Config,
              side_a: ChainId, side_b: ChainId,
              a_chan: ChannelId, b_chan: ChannelId,
              port_id: PortId = PortId('transfer')):

    pkt_send_a = packet_send(c, side_a, side_b, port_id,
                             a_chan, amount=9999, height_offset=1000)

    split()

    pkt_recv_b = packet_recv(c, side_b, side_a, port_id, a_chan)

    if pkt_send_a.sequence != pkt_recv_b.sequence:
        l.error(
            f'Mismatched sequence numbers for path {side_a} -> {side_b} : Sent={pkt_send_a.sequence} versus Received={pkt_recv_b.sequence}')

    split()

    # write the ack
    pkt_ack_a = packet_ack(c, side_a, side_b, port_id, b_chan)

    if pkt_recv_b.sequence != pkt_ack_a.sequence:
        l.error(
            f'Mismatched sequence numbers for ack on path {side_a} -> {side_b} : Recv={pkt_recv_b.sequence} versus Ack={pkt_ack_a.sequence}')

    split()

    pkt_send_b = packet_send(c, side_b, side_a, port_id,
                             b_chan, amount=9999, height_offset=1000)

    split()

    pkt_recv_a = packet_recv(c, side_a, side_b, port_id, b_chan)

    if pkt_send_b.sequence != pkt_recv_a.sequence:
        l.error(
            f'Mismatched sequence numbers for path {side_b} -> {side_a} : Sent={pkt_send_b.sequence} versus Received={pkt_recv_a.sequence}')

    split()

    pkt_ack_b = packet_ack(c, side_b, side_a, port_id, a_chan)

    if pkt_recv_a.sequence != pkt_ack_b.sequence:
        l.error(
            f'Mismatched sequence numbers for ack on path {side_a} -> {side_b} : Recv={pkt_recv_a.sequence} versus Ack={pkt_ack_b.sequence}')


def timeout(c: Config,
            side_a: ChainId, side_b: ChainId,
            a_chan: ChannelId, b_chan: ChannelId,
            port_id: PortId = PortId('transfer')):

    pkt_send_a = packet_send(c, side_a, side_b, port_id,
                             a_chan, amount=9999, height_offset=1)

    split()

    pkt_timeout_a = packet_timeout(c, side_b, side_a, port_id, a_chan)

    if pkt_send_a.sequence != pkt_timeout_a.sequence:
        l.error(
            f'Mismatched sequence numbers for path {side_a} -> {side_b} : Sent={pkt_send_a.sequence} versus Timeout={pkt_timeout_a.sequence}')

    split()

    pkt_send_b = packet_send(c, side_b, side_a, port_id,
                             b_chan, amount=9999, height_offset=1)

    split()

    pkt_timeout_b = packet_timeout(c, side_a, side_b, port_id, b_chan)

    if pkt_send_b.sequence != pkt_timeout_b.sequence:
        l.error(
            f'Mismatched sequence numbers for path {side_b} -> {side_a} : Sent={pkt_send_b.sequence} versus Timeout={pkt_timeout_b.sequence}')

    split()


def find_entry(result: Any, key: str) -> Any:
    for entry in result:
        if key in entry:
            return entry[key]
