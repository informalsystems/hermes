from typing import Any, List

from time import sleep
from dataclasses import dataclass

import logging as l

from .cmd import *
from .common import *


@dataclass
class TxPacketSendRes:
    sequence: Sequence


@cmd("tx raw packet-send")
@dataclass
class TxPacketSend(Cmd[TxPacketSendRes]):
    src_chain_id: str
    dst_chain_id: str
    src_port: PortId
    src_channel: ChannelId

    def args(self) -> List[str]:
        return [self.src_chain_id, self.dst_chain_id, self.src_port, self.src_channel, "9999", "1000"]

    def process(self, result: Any) -> TxPacketSendRes:
        return from_dict(TxPacketSendRes, result[0][0]['SendPacketChannel']['packet'])

# -----------------------------------------------------------------------------


@dataclass
class TxPacketRecvRes:
    sequence: Sequence


@cmd("tx raw packet-recv")
@dataclass
class TxPacketRecv(Cmd[TxPacketRecvRes]):
    src_chain_id: ChainId
    dst_chain_id: ChainId
    src_port: PortId
    src_channel: ChannelId

    def args(self) -> List[str]:
        return [self.dst_chain_id, self.src_chain_id, self.src_port, self.src_channel]

    # todo: the output here is a list of [`UpdateClient`,`WriteAcknowledgementChannel`]
    #   possible that the UpdateClient is missing, and then `WriteAcknowledgementChannel` will no longer be at index 1
    #   so we might need a more sophisticated way to extract this event...
    def process(self, result: Any) -> TxPacketRecvRes:
        return from_dict(TxPacketRecvRes, result[0][1]['WriteAcknowledgementChannel']['packet'])

# -----------------------------------------------------------------------------


@dataclass
class TxPacketAckRes:
    sequence: Sequence


@cmd("tx raw packet-ack")
@dataclass
class TxPacketAck(Cmd[TxPacketAckRes]):
    src_chain_id: ChainId
    dst_chain_id: ChainId
    src_port: PortId
    src_channel: ChannelId

    def args(self) -> List[str]:
        return [self.dst_chain_id, self.src_chain_id, self.src_port, self.src_channel]

    # todo: same as for TxPacketRecv:
    #   the output here is a list of [`UpdateClient`,`AcknowledgePacketChannel`]
    #   possible that the UpdateClient is missing, and then `WriteAcknowledgementChannel` will no longer be at index 1
    #   so we might need a more sophisticated way to extract this event...
    def process(self, result: Any) -> TxPacketAckRes:
        return from_dict(TxPacketAckRes, result[0][1]['AcknowledgePacketChannel']['packet'])

# -----------------------------------------------------------------------------


# TRANSFER (packet send)
# =============================================================================

def packet_send(c: Config, src: ChainId, dst: ChainId, src_port: PortId, src_channel: ChannelId) -> Sequence:
    cmd = TxPacketSend(src_chain_id=src, dst_chain_id=dst,
                       src_port=src_port, src_channel=src_channel)

    res = cmd.run(c).success()
    l.info(f'PacketSend to {src} and obtained sequence number {res.sequence}')
    return res.sequence


def packet_recv(c: Config, dst: ChainId, src: ChainId, src_port: PortId, src_channel: ChannelId) -> Sequence:
    cmd = TxPacketRecv(src_chain_id=src, dst_chain_id=dst,
                       src_port=src_port, src_channel=src_channel)

    res = cmd.run(c).success()
    l.info(f'PacketRecv to {dst} done for sequence number {res.sequence}')
    return res.sequence


def packet_ack(c: Config, dst: ChainId, src: ChainId, src_port: PortId, src_channel: ChannelId) -> Sequence:
    cmd = TxPacketAck(src_chain_id=src, dst_chain_id=dst,
                      src_port=src_port, src_channel=src_channel)

    res = cmd.run(c).success()
    l.info(f'PacketAck to {dst} done for sequence number {res.sequence}')
    return res.sequence


def ping_pong(c: Config,
              side_a: ChainId, side_b: ChainId,
              a_chan: ChannelId, b_chan: ChannelId,
              port_id: PortId = PortId('transfer')):

    seq_send_a = packet_send(c, side_a, side_b, port_id, a_chan)

    split()

    seq_recv_a = packet_recv(c, side_b, side_a, port_id, b_chan)

    if seq_send_a != seq_recv_a:
        l.error(
            f'Mismatched sequence numbers for path {side_a} -> {side_b} : Sent={seq_send_a} versus Received={seq_recv_a}')

    split()

    # write the ack
    seq_ack_a = packet_ack(c, side_a, side_b, port_id, a_chan)
    if seq_recv_a != seq_ack_a:
        l.error(
            f'Mismatched sequence numbers for ack on path {side_a} -> {side_b} : Recv={seq_recv_a} versus Ack={seq_ack_a}')

    split()

    seq_send_b = packet_send(c, side_b, side_a, port_id, b_chan)

    split()

    seq_recv_b = packet_recv(c, side_a, side_b, port_id, a_chan)

    if seq_send_b != seq_recv_b:
        l.error(
            f'Mismatched sequence numbers for path {side_b} -> {side_b} : Sent={seq_send_b} versus Received={seq_recv_b}')

    split()

    seq_ack_b = packet_ack(c, side_b, side_a, port_id, a_chan)

    if seq_recv_b != seq_ack_b:
        l.error(
            f'Mismatched sequence numbers for ack on path {side_a} -> {side_b} : Recv={seq_recv_b} versus Ack={seq_ack_b}')
