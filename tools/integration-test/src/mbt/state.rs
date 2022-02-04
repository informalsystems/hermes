use serde::{Deserialize, Serialize};

use super::itf::{Map, Set};

type ChainId = String;
type PortId = String;
type DenomId = String;
type ChannelId = isize;
type AccountId = isize;
type PacketId = isize;

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ChannelEndpoint {
    pub chain_id: ChainId,
    pub port_id: PortId,
    pub channel_id: ChannelId,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Channel {
    pub source: ChannelEndpoint,
    pub target: ChannelEndpoint,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Packet {
    pub id: PacketId,
    pub channel: Channel,
    pub from: AccountId,
    pub to: AccountId,
    pub denom: DenomId,
    pub amount: isize,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LocalPackets {
    pub list: Map<PacketId, Packet>,
    pub pending: Set<PacketId>,
    pub expired: Set<PacketId>,
    pub success: Set<PacketId>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Ics20 {
    pub port_id: PortId,
    pub escrow: Map<ChannelId, AccountId>,
    pub channel: Map<ChainId, ChannelId>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Chain {
    pub id: ChainId,
    pub ports: Set<PortId>,
    pub channel: Map<ChannelId, Channel>,
    pub active_channels: Set<ChannelId>,
    pub bank: Map<AccountId, Map<DenomId, isize>>,
    pub supply: Map<DenomId, isize>,
    pub local_packets: LocalPackets,
    pub remote_packets: Map<ChannelId, Map<PacketId, Packet>>,
    pub ics20: Ics20,
    pub next_channel_id: ChannelId,
    pub next_packet_id: PacketId,
    pub next_account_id: AccountId,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "name")]
pub enum Action {
    Null,
    LocalTransfer {
        source: AccountId,
        target: AccountId,
        denom: DenomId,
        amount: isize,
    },
    CreateChannel {
        chains: Set<ChainId>,
    },
    ExpireChannel {
        chains: Set<ChainId>,
    },
    IBCTransferSendPacket {
        packet: Packet,
    },
    IBCTransferReceivePacket {
        packet: Packet,
    },
    IBCTransferAcknowledgePacket {
        packet: Packet,
    },
    IBCTransferTimeoutPacket {
        packet: Packet,
    },
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "name")]
pub enum Outcome {
    Success,
    Error,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct State {
    pub chains: Map<ChainId, Chain>,
    pub action: Action,
    pub outcome: Outcome,
}
