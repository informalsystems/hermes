from typing import Any, List

from time import sleep
from dataclasses import dataclass

import logging as l

from .cmd import *
from .common import *


@dataclass
class Packet:
    sequence: Sequence
    source_port: PortId
    source_channel: ChannelId
    destination_port: PortId
    destination_channel: ChannelId
    data: bytes
    timeout_height: Height
    timeout_timestamp: Timestamp


@dataclass
class TxPacketSendRes:
    height: BlockHeight
    packet: Packet


@cmd("tx raw packet-send")
@dataclass
class TxPacketSend(Cmd[TxPacketSendRes]):
    src_chain_id: ChainId
    dst_chain_id: ChainId
    src_port: PortId
    src_channel: ChannelId

    def args(self) -> List[str]:
        return [self.src_chain_id, self.dst_chain_id, self.src_port, self.src_channel, "9999", "1000"]

    def process(self, result: Any) -> TxPacketSendRes:
        entry = find_entry(result[0], 'SendPacketChannel')
        return from_dict(TxPacketSendRes, entry)

# -----------------------------------------------------------------------------


@dataclass
class TxPacketRecvRes:
    height: BlockHeight
    packet: Packet
    ack: bytes


@cmd("tx raw packet-recv")
@dataclass
class TxPacketRecv(Cmd[TxPacketRecvRes]):
    src_chain_id: ChainId
    dst_chain_id: ChainId
    src_port: PortId
    src_channel: ChannelId

    def args(self) -> List[str]:
        return [self.dst_chain_id, self.src_chain_id, self.src_port, self.src_channel]

    def process(self, result: Any) -> TxPacketRecvRes:
        entry = find_entry(result[0], 'WriteAcknowledgementChannel')
        return from_dict(TxPacketRecvRes, entry)

# -----------------------------------------------------------------------------


@dataclass
class TxPacketAckRes:
    height: BlockHeight
    packet: Packet


@cmd("tx raw packet-ack")
@dataclass
class TxPacketAck(Cmd[TxPacketAckRes]):
    src_chain_id: ChainId
    dst_chain_id: ChainId
    src_port: PortId
    src_channel: ChannelId

    def args(self) -> List[str]:
        return [self.dst_chain_id, self.src_chain_id, self.src_port, self.src_channel]

    def process(self, result: Any) -> TxPacketAckRes:
        entry = find_entry(result[0], 'AcknowledgePacketChannel')
        return from_dict(TxPacketAckRes, entry)

# =============================================================================
# TRANSFER (packet send)
# =============================================================================


def packet_send(c: Config, src: ChainId, dst: ChainId, src_port: PortId, src_channel: ChannelId) -> Packet:
    cmd = TxPacketSend(src_chain_id=src, dst_chain_id=dst,
                       src_port=src_port, src_channel=src_channel)

    res = cmd.run(c).success()
    l.info(
        f'PacketSend to {src} and obtained sequence number {res.packet.sequence}')

    return res.packet


def packet_recv(c: Config, dst: ChainId, src: ChainId, src_port: PortId, src_channel: ChannelId) -> Packet:
    cmd = TxPacketRecv(src_chain_id=src, dst_chain_id=dst,
                       src_port=src_port, src_channel=src_channel)

    res = cmd.run(c).success()
    l.info(
        f'PacketRecv to {dst} done for sequence number {res.packet.sequence}')

    return res.packet


def packet_ack(c: Config, dst: ChainId, src: ChainId, src_port: PortId, src_channel: ChannelId) -> Packet:
    cmd = TxPacketAck(src_chain_id=src, dst_chain_id=dst,
                      src_port=src_port, src_channel=src_channel)

    res = cmd.run(c).success()
    l.info(
        f'PacketAck to {dst} done for sequence number {res.packet.sequence}')

    return res.packet


def ping_pong(c: Config,
              side_a: ChainId, side_b: ChainId,
              a_chan: ChannelId, b_chan: ChannelId,
              port_id: PortId = PortId('transfer')):

    pkt_send_a = packet_send(c, side_a, side_b, port_id, a_chan)

    split()

    pkt_recv_a = packet_recv(c, side_b, side_a, port_id, b_chan)

    if pkt_send_a.sequence != pkt_recv_a.sequence:
        l.error(
            f'Mismatched sequence numbers for path {side_a} -> {side_b} : Sent={pkt_send_a.sequence} versus Received={pkt_recv_a.sequence}')

    split()

    # write the ack
    pkt_ack_a = packet_ack(c, side_a, side_b, port_id, a_chan)

    if pkt_recv_a.sequence != pkt_ack_a.sequence:
        l.error(
            f'Mismatched sequence numbers for ack on path {side_a} -> {side_b} : Recv={pkt_recv_a.sequence} versus Ack={pkt_ack_a.sequence}')

    split()

    pkt_send_b = packet_send(c, side_b, side_a, port_id, b_chan)

    split()

    pkt_recv_b = packet_recv(c, side_a, side_b, port_id, a_chan)

    if pkt_send_b.sequence != pkt_recv_b.sequence:
        l.error(
            f'Mismatched sequence numbers for path {side_b} -> {side_b} : Sent={pkt_send_b.sequence} versus Received={pkt_recv_b.sequence}')

    split()

    pkt_ack_b = packet_ack(c, side_b, side_a, port_id, a_chan)

    if pkt_recv_b.sequence != pkt_ack_b.sequence:
        l.error(
            f'Mismatched sequence numbers for ack on path {side_a} -> {side_b} : Recv={pkt_recv_b.sequence} versus Ack={pkt_ack_b.sequence}')


def find_entry(result: Any, key: str) -> Any:
    for entry in result:
        if key in entry:
            return entry[key]
