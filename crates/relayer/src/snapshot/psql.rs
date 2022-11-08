use std::borrow::Cow;

use async_trait::async_trait;
use bigdecimal::BigDecimal;
use sqlx::PgPool;
use sqlx::{postgres::PgRow, types::Json};

use crate::snapshot::util::bigdecimal_to_u64;
use crate::snapshot::IbcData;
use crate::{chain::requests::QueryHeight, error::Error};

use super::{IbcSnapshot, SnapshotStore, KEEP_SNAPSHOTS};

pub struct PsqlSnapshotStore {
    pool: PgPool,
    // cache: HashMap<u64, IbcSnapshot>,
}

impl PsqlSnapshotStore {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }
}

#[async_trait]
impl SnapshotStore for PsqlSnapshotStore {
    async fn fetch_snapshot(
        &self,
        query_height: QueryHeight,
    ) -> Result<Cow<'_, IbcSnapshot>, Error> {
        // let snapshot = match query_height {
        //     QueryHeight::Specific(height) if self.cache.contains_key(&height.revision_height()) => {
        //         let snapshot = self.cache.get(&height.revision_height()).unwrap();
        //         Cow::Borrowed(snapshot)
        //     }
        //     query_height => {
        //         let snapshot = fetch_snapshot(&self.pool, query_height).await?;
        //         Cow::Owned(snapshot)
        //     }
        // };

        let snapshot = fetch_snapshot(&self.pool, query_height).await?;
        Ok(Cow::Owned(snapshot))
    }

    async fn update_snapshot(&mut self, snapshot: &IbcSnapshot) -> Result<(), Error> {
        update_snapshot(&self.pool, snapshot).await
    }

    async fn vacuum_snapshots(&mut self, at_or_below: u64) -> Result<(), Error> {
        vacuum_snapshots(&self.pool, at_or_below).await
    }
}

/// Create the `ibc_json` table if it does not exists yet
#[tracing::instrument(skip(pool))]
pub async fn create_table(pool: &PgPool) -> Result<(), Error> {
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

#[tracing::instrument(skip(pool))]
pub async fn fetch_snapshot(
    pool: &PgPool,
    query_height: QueryHeight,
) -> Result<IbcSnapshot, Error> {
    crate::time!("fetch_snapshot");

    let query = match query_height {
        QueryHeight::Latest => {
            sqlx::query_as::<_, IbcSnapshot>("SELECT * FROM ibc_json ORDER BY height DESC LIMIT 1")
        }
        QueryHeight::Specific(h) => {
            sqlx::query_as::<_, IbcSnapshot>("SELECT * FROM ibc_json WHERE height = $1 LIMIT 1")
                .bind(BigDecimal::from(h.revision_height()))
        }
    };

    query.fetch_one(pool).await.map_err(Error::sqlx)
}

#[tracing::instrument(skip(pool, snapshot))]
pub async fn update_snapshot(pool: &PgPool, snapshot: &IbcSnapshot) -> Result<(), Error> {
    crate::time!("update_snapshot");

    // create the ibc table if it does not exist
    create_table(pool).await?;

    let height = BigDecimal::from(snapshot.height);
    let data = Json(&snapshot.data);

    // println!("{}", serde_json::to_string_pretty(&snapshot.data).unwrap());

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

#[tracing::instrument(skip(pool))]
async fn vacuum_snapshots(pool: &PgPool, at_or_below: u64) -> Result<(), Error> {
    sqlx::query("DELETE FROM ibc_json WHERE height <= $1")
        .bind(BigDecimal::from(at_or_below))
        .execute(pool)
        .await
        .map_err(Error::sqlx)?;

    Ok(())
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
