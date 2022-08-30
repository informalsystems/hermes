use std::collections::HashMap;

use bigdecimal::BigDecimal;
use serde::de::{Deserializer, Error as _};
use serde::{Deserialize, Serialize, Serializer};
use sqlx::postgres::PgRow;
use sqlx::types::Json;

use ibc::core::ics02_client::client_consensus::AnyConsensusStateWithHeight;
use ibc::core::ics02_client::client_state::IdentifiedAnyClientState;
use ibc::core::ics03_connection::connection::IdentifiedConnectionEnd;
use ibc::core::ics04_channel::channel::IdentifiedChannelEnd;
use ibc::core::ics04_channel::packet::{Packet, Sequence};
use ibc::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortChannelId, PortId};
use ibc::Height;

use crate::chain::endpoint::ChainStatus;

pub mod memory;
pub mod psql;

pub const KEEP_SNAPSHOTS: u64 = 8;

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd)]
pub struct PacketId {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub sequence: Sequence,
}

impl Serialize for PacketId {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&format!(
            "{}/{}/{}",
            self.port_id, self.channel_id, self.sequence
        ))
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

// TODO: Consider:
//
// - to help with reducing RPCs from update client
//   (update on NewBlock event, beefed up with block data, probably still the validators RPC is needed)
// pub signed_header: SignedHeader,
// pub validator_set: ValidatorSet,
//
// - to get clients, their state and consensus states, etc
//   (update on create and update client events)
//
// - to help with packet acknowledgments...this is tricky as we need to pass from
//   the counterparty chain:
//     1. data (seqs for packets with commitments) on start
//     2. Acknowledge and Timeout packet events in order to clear
// pub pending_ack_packets: HashMap<PacketId, Packet>,
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct IbcData {
    pub app_status: ChainStatus,

    pub connections: HashMap<ConnectionId, IdentifiedConnectionEnd>,
    pub channels: HashMap<PortChannelId, IdentifiedChannelEnd>,

    pub client_states: HashMap<ClientId, IdentifiedAnyClientState>,
    pub consensus_states: HashMap<(ClientId, Height), AnyConsensusStateWithHeight>,

    pub pending_sent_packets: HashMap<PacketId, Packet>, // TODO - use IbcEvent val (??)
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct IbcSnapshot {
    pub height: u64,
    pub data: IbcData,
}

impl<'r> sqlx::FromRow<'r, PgRow> for IbcSnapshot {
    fn from_row(row: &'r PgRow) -> Result<Self, sqlx::Error> {
        use sqlx::Row;

        let height: BigDecimal = row.try_get("height")?;
        let data: Json<IbcData> = row.try_get("data")?;

        Ok(IbcSnapshot {
            height: bigdecimal_to_u64(height),
            data: data.0,
        })
    }
}

fn bigdecimal_to_u64(b: BigDecimal) -> u64 {
    assert!(b.is_integer());
    let (bigint, _) = b.as_bigint_and_exponent();
    let (sign, digits) = bigint.to_u64_digits();
    assert!(sign == bigdecimal::num_bigint::Sign::Plus);
    assert!(digits.len() == 1);
    digits[0]
}
