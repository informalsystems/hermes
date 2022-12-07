use core::fmt;
use std::collections::HashMap;

use ibc_relayer_types::core::ics04_channel::events::SendPacket;
use ibc_relayer_types::Height;
use serde::de::{Deserializer, Error as _};
use serde::{Deserialize, Serialize, Serializer};

use ibc_relayer_types::core::ics03_connection::connection::IdentifiedConnectionEnd;
use ibc_relayer_types::core::ics04_channel::channel::IdentifiedChannelEnd;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics24_host::identifier::{
    ChannelId, ClientId, ConnectionId, PortChannelId, PortId,
};

use crate::chain::endpoint::ChainStatus;
use crate::client_state::IdentifiedAnyClientState;
use crate::consensus_state::AnyConsensusStateWithHeight;

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct IbcSnapshot {
    pub height: u64,
    pub data: IbcData,
}

// TODO: Consider:
//
// - to help with reducing RPCs from update client
//   (update on NewBlock event, beefed up with block data, probably still the validators RPC is needed)
//
//   pub signed_header: SignedHeader,
//   pub validator_set: ValidatorSet,
//
// - update  clients, their state and consensus states on create and update client events
//
// - to help with packet acknowledgments...this is tricky as we need to pass from
//   the counterparty chain:
//     1. data (seqs for packets with commitments) on start
//     2. Acknowledge and Timeout packet events in order to clear
//
//   pub pending_ack_packets: HashMap<PacketId, Packet>,
//
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct IbcData {
    pub app_status: ChainStatus,

    pub connections: HashMap<ConnectionId, IdentifiedConnectionEnd>,
    pub channels: HashMap<Key<PortChannelId>, IdentifiedChannelEnd>,

    pub client_states: HashMap<ClientId, IdentifiedAnyClientState>,
    pub consensus_states: HashMap<ClientId, Vec<AnyConsensusStateWithHeight>>,

    pub pending_sent_packets: HashMap<PacketId, SendPacket>,
}

impl Default for IbcData {
    fn default() -> Self {
        Self {
            app_status: ChainStatus {
                height: Height::new(1, 1).unwrap(),
                timestamp: Default::default(),
            },
            connections: Default::default(),
            channels: Default::default(),
            client_states: Default::default(),
            consensus_states: Default::default(),
            pending_sent_packets: Default::default(),
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct PacketId {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub sequence: Sequence,
}

impl fmt::Display for PacketId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}/{}", self.port_id, self.channel_id, self.sequence)
    }
}

impl Serialize for PacketId {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.to_string())
    }
}

impl<'de> Deserialize<'de> for PacketId {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let data = <&str>::deserialize(deserializer)?;
        let parts: [_; 3] = data
            .splitn(3, '/')
            .collect::<Vec<_>>()
            .as_slice()
            .try_into()
            .map_err(D::Error::custom)?;

        let [port_id, channel_id, sequence] = parts;

        let port_id: PortId = port_id.parse().map_err(D::Error::custom)?;
        let channel_id: ChannelId = channel_id.parse().map_err(D::Error::custom)?;
        let sequence: Sequence = sequence.parse().map_err(D::Error::custom)?;

        Ok(Self {
            port_id,
            channel_id,
            sequence,
        })
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Key<A>(pub A);

impl Serialize for Key<PortChannelId> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&format!("{}:{}", self.0.channel_id, self.0.port_id))
    }
}

impl<'de> Deserialize<'de> for Key<PortChannelId> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let data = <&str>::deserialize(deserializer)?;
        let parts: [_; 2] = data
            .splitn(2, ':')
            .collect::<Vec<_>>()
            .as_slice()
            .try_into()
            .map_err(D::Error::custom)?;

        let [channel_id, port_id] = parts;

        let channel_id: ChannelId = channel_id.parse().map_err(D::Error::custom)?;
        let port_id: PortId = port_id.parse().map_err(D::Error::custom)?;

        Ok(Self(PortChannelId::new(channel_id, port_id)))
    }
}
