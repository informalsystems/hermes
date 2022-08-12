use bigdecimal::BigDecimal;
use sqlx::types::Json;
use sqlx::PgPool;

use crate::error::Error;

use super::{IbcSnapshot, KEEP_SNAPSHOTS};

/// Create the `ibc_json` table if it does not exists yet
#[tracing::instrument(skip(pool))]
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

#[tracing::instrument(skip(pool, snapshot))]
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

#[tracing::instrument(skip(pool))]
async fn vacuum_snapshots(pool: &PgPool, at_or_below: u64) -> Result<(), Error> {
    sqlx::query("DELETE FROM ibc_json WHERE height <= $1")
        .bind(BigDecimal::from(at_or_below))
        .execute(pool)
        .await
        .map_err(Error::sqlx)?;

    Ok(())
}
