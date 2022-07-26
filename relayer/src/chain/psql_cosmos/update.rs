use ibc::core::ics24_host::identifier::{ChannelId, ConnectionId, PortId};

use ibc::core::ics03_connection::connection::IdentifiedConnectionEnd;
use serde::de::{Deserializer, Error as _};
use serde::{Deserialize, Serialize, Serializer};

use sqlx::PgPool;
use std::collections::HashMap;

use ibc::core::ics04_channel::channel::IdentifiedChannelEnd;
use ibc::core::ics04_channel::packet::{Packet, Sequence};

use crate::error::Error;

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

#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct IbcData {
    pub connections: HashMap<ConnectionId, IdentifiedConnectionEnd>,
    pub channels: HashMap<ChannelId, IdentifiedChannelEnd>, // TODO - use PortChannelId key
    pub pending_sent_packets: HashMap<PacketId, Packet>,    // TODO - use IbcEvent val (??)
                                                            // ..
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct IbcSnapshot {
    pub height: u64,
    pub json_data: IbcData,
}

pub async fn update_dbs(pool: &PgPool, snapshot: &IbcSnapshot) -> Result<(), Error> {
    // create the ibc table if it does not exist
    sqlx::query(
        r#"
        CREATE TABLE IF NOT EXISTS ibc_json (
            height DOUBLE PRECISION PRIMARY KEY,
            json_data JSONB
        );"#,
    )
    .execute(pool)
    .await
    .map_err(Error::sqlx)?;

    // insert the json blob, update if already there
    let json_blob = serde_json::to_string(&snapshot).unwrap();
    let sql_insert_cmd = format!(
        "INSERT INTO ibc_json SELECT height, json_data \
        FROM json_populate_record(NULL::ibc_json, '{}') \
        ON CONFLICT (height) DO UPDATE SET json_data=EXCLUDED.json_data",
        json_blob
    );
    sqlx::query(sql_insert_cmd.as_str())
        .execute(pool)
        .await
        .map_err(Error::sqlx)?;
    Ok(())
}
