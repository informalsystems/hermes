use std::collections::HashMap;

use bigdecimal::BigDecimal;
use serde::de::{Deserializer, Error as _};
use serde::{Deserialize, Serialize, Serializer};
use sqlx::PgPool;

use ibc::core::ics03_connection::connection::IdentifiedConnectionEnd;
use ibc::core::ics04_channel::channel::IdentifiedChannelEnd;
use ibc::core::ics04_channel::packet::{Packet, Sequence};
use ibc::core::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use sqlx::postgres::PgRow;
use sqlx::types::Json;

use crate::chain::endpoint::ChainStatus;
use crate::error::Error;

const KEEP_SNAPSHOTS: u64 = 8;

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
        let mut parts = data.splitn(3, '/');
        let port_id: PortId = parts.next().unwrap().parse().map_err(D::Error::custom)?;
        let channel_id: ChannelId = parts.next().unwrap().parse().map_err(D::Error::custom)?;
        let sequence: Sequence = parts.next().unwrap().parse().map_err(D::Error::custom)?;
        Ok(Self {
            port_id,
            channel_id,
            sequence,
        })
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct IbcData {
    pub app_status: ChainStatus,
    pub connections: HashMap<ConnectionId, IdentifiedConnectionEnd>,
    pub channels: HashMap<ChannelId, IdentifiedChannelEnd>, // TODO - use PortChannelId key
    pub pending_sent_packets: HashMap<PacketId, Packet>,    // TODO - use IbcEvent val (??)
                                                            // TODO consider:
                                                            // - to help with reducing RPCs from update client
                                                            //   (update on NewBlock event, beefed up with block data, probably still the validators RPC is needed)
                                                            // pub signed_header: SignedHeader,
                                                            // pub validator_set: ValidatorSet,
                                                            // - to get clients, their state and consensus states, etc
                                                            //   (update on create and update client events)
                                                            // pub client_states: HashMap<ClientId, ClientState>
                                                            // pub consensus_states: HashMap<(ClientId, Height), ConsensusState>
                                                            // - to help with packet acknowledgments...this is tricky as we need to pass from
                                                            //   the counterparty chain:
                                                            //     1. data (seqs for packets with commitments) on start
                                                            //     2. Acknowledge and Timeout packet events in order to clear
                                                            // pub pending_ack_packets: HashMap<PacketId, Packet>,
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

/// Create the `ibc_json` table if it does not exists yet
pub async fn create_table(pool: &PgPool) -> Result<(), Error> {
    crate::time!("create_table");

    sqlx::query(
        "CREATE TABLE IF NOT EXISTS ibc_json ( \
            height NUMERIC PRIMARY KEY, \
            data JSONB \
        );",
    )
    .execute(pool)
    .await
    .map_err(Error::sqlx)?;

    Ok(())
}

pub async fn update_snapshot(pool: &PgPool, snapshot: &IbcSnapshot) -> Result<(), Error> {
    crate::time!("update_snapshot");

    // create the ibc table if it does not exist
    create_table(pool).await?;

    let height = BigDecimal::from(snapshot.height);
    let data = Json(&snapshot.data);

    // insert the json blob, update if already there
    let query = "INSERT INTO ibc_json (height, data) VALUES ($1, $2) \
                 ON CONFLICT (height) DO UPDATE SET data = EXCLUDED.data";

    sqlx::query(query)
        .bind(height)
        .bind(data)
        .execute(pool)
        .await
        .map_err(Error::sqlx)?;

    // delete oldest snapshots
    if snapshot.height > KEEP_SNAPSHOTS {
        let at_or_below = snapshot.height - KEEP_SNAPSHOTS;
        vacuum_snapshots(pool, at_or_below).await?;
    }

    Ok(())
}

async fn vacuum_snapshots(pool: &PgPool, at_or_below: u64) -> Result<(), Error> {
    // we need to format! here because sqlx does not support u64 bindings, only i64
    sqlx::query("DELETE FROM ibc_json WHERE height <= $1")
        .bind(BigDecimal::from(at_or_below))
        .execute(pool)
        .await
        .map_err(Error::sqlx)?;

    Ok(())
}
