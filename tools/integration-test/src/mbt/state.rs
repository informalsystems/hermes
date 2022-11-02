use serde::{Deserialize, Serialize};

use super::itf::{Map, Set};

pub type ChainId = u128;
pub type DenomId = ChainId;
pub type AccountId = u128;
pub type PacketId = u128;
pub type Balance = u128;

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Packet {
    pub id: PacketId,
    pub from: AccountId,
    pub source_chain_id: ChainId,
    pub to: AccountId,
    pub target_chain_id: ChainId,
    pub denom: DenomId,
    pub amount: Balance,
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
pub struct Chain {
    pub id: ChainId,
    pub bank: Map<AccountId, Map<DenomId, Balance>>,
    pub supply: Map<DenomId, Balance>,
    pub local_packets: LocalPackets,
    pub remote_packets: Map<ChainId, Map<PacketId, Packet>>,
    pub escrow: Map<ChainId, Map<DenomId, Balance>>,
    pub next_packet_id: PacketId,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "name")]
pub enum Action {
    Null,
    #[serde(rename_all = "camelCase")]
    LocalTransfer {
        chain_id: ChainId,
        source: AccountId,
        target: AccountId,
        denom: DenomId,
        amount: Balance,
    },
    RestoreRelay,
    InterruptRelay,
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
