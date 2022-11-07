use std::borrow::Cow;
use std::collections::BTreeMap;

use async_trait::async_trait;

use crate::chain::requests::QueryHeight;
use crate::error::Error;

use super::{IbcSnapshot, SnapshotStore, KEEP_SNAPSHOTS};

#[derive(Default)]
pub struct MemorySnapshotStore {
    snapshots: BTreeMap<u64, IbcSnapshot>,
}

impl MemorySnapshotStore {
    pub fn new() -> Self {
        Self::default()
    }
}

#[async_trait]
impl SnapshotStore for MemorySnapshotStore {
    async fn fetch_snapshot(
        &self,
        query_height: QueryHeight,
    ) -> Result<Cow<'_, IbcSnapshot>, Error> {
        match query_height {
            QueryHeight::Latest => match self.snapshots.values().next_back() {
                Some(snapshot) => Ok(Cow::Borrowed(snapshot)),
                None => todo!(),
            },
            QueryHeight::Specific(height) => match self.snapshots.get(&height.revision_height()) {
                Some(snapshot) => Ok(Cow::Borrowed(snapshot)),
                None => todo!(),
            },
        }
    }

    async fn update_snapshot(&mut self, snapshot: &IbcSnapshot) -> Result<(), Error> {
        // delete oldest snapshots
        if snapshot.height > KEEP_SNAPSHOTS {
            let at_or_below = snapshot.height - KEEP_SNAPSHOTS;
            self.vacuum_snapshots(at_or_below).await?;
        }

        self.snapshots.insert(snapshot.height, snapshot.clone());

        Ok(())
    }

    async fn vacuum_snapshots(&mut self, at_or_below: u64) -> Result<(), Error> {
        let to_remove: Vec<_> = self
            .snapshots
            .keys()
            .filter(|&&height| height <= at_or_below)
            .copied()
            .collect();

        for key in to_remove {
            self.snapshots.remove(&key);
        }

        Ok(())
    }
}
