use std::borrow::Cow;

use async_trait::async_trait;

pub mod memory;
pub mod psql;
mod util;

mod data;
pub use data::*;

use ibc_relayer_types::core::ics03_connection::connection::IdentifiedConnectionEnd;
use ibc_relayer_types::core::ics04_channel::channel::IdentifiedChannelEnd;
use ibc_relayer_types::core::ics04_channel::events::SendPacket;
use ibc_relayer_types::core::ics24_host::identifier::{ClientId, ConnectionId, PortChannelId};
use ibc_relayer_types::Height;

use crate::chain::endpoint::ChainStatus;
use crate::chain::psql_cosmos::PsqlError;
use crate::chain::requests::*;
use crate::client_state::{AnyClientState, IdentifiedAnyClientState};
use crate::consensus_state::{AnyConsensusState, AnyConsensusStateWithHeight};
use crate::error::Error;

pub const KEEP_SNAPSHOTS: u64 = 8;

#[async_trait]
pub trait SnapshotStore: Send + Sync {
    async fn fetch_snapshot(
        &self,
        query_height: QueryHeight,
    ) -> Result<Cow<'_, IbcSnapshot>, Error>;

    async fn update_snapshot(&mut self, snapshot: &IbcSnapshot) -> Result<(), Error>;

    async fn vacuum_snapshots(&mut self, at_or_below: u64) -> Result<(), Error>;

    #[tracing::instrument(skip(self))]
    async fn query_application_status(&self) -> Result<ChainStatus, Error> {
        let result = self.fetch_snapshot(QueryHeight::Latest).await?;
        Ok(result.data.app_status)
    }

    #[tracing::instrument(skip(self))]
    async fn query_connections(
        &self,
        query_height: QueryHeight,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
        let result = self.fetch_snapshot(query_height).await?;
        Ok(result.data.connections.values().cloned().collect())
    }

    #[tracing::instrument(skip(self))]
    async fn query_client_connections(
        &self,
        query_height: QueryHeight,
        client_id: &ClientId,
    ) -> Result<Vec<ConnectionId>, Error> {
        let result = self.fetch_snapshot(query_height).await?;

        let connections = result
            .data
            .connections
            .values()
            .filter_map(|connection| {
                connection
                    .connection_end
                    .client_id_matches(client_id)
                    .then(|| connection.connection_id.clone())
            })
            .collect();

        Ok(connections)
    }

    #[tracing::instrument(skip(self))]
    async fn query_connection(
        &self,
        query_height: QueryHeight,
        id: &ConnectionId,
    ) -> Result<Option<IdentifiedConnectionEnd>, Error> {
        let result = self.fetch_snapshot(query_height).await?;
        Ok(result.data.connections.get(id).cloned())
    }

    #[tracing::instrument(skip(self))]
    async fn query_channels(
        &self,
        query_height: QueryHeight,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        let result = self.fetch_snapshot(query_height).await?;
        Ok(result.data.channels.values().cloned().collect())
    }

    #[tracing::instrument(skip(self))]
    async fn query_connection_channels(
        &self,
        query_height: QueryHeight,
        connection_id: &ConnectionId,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        let result = self.fetch_snapshot(query_height).await?;
        Ok(result
            .data
            .channels
            .values()
            .cloned()
            .filter(|ch| ch.channel_end.connection_hops.first() == Some(connection_id))
            .collect())
    }

    #[tracing::instrument(skip(self))]
    async fn query_channel(
        &self,
        query_height: QueryHeight,
        id: &PortChannelId,
    ) -> Result<Option<IdentifiedChannelEnd>, Error> {
        let result = self.fetch_snapshot(query_height).await?;
        Ok(result.data.channels.get(&Key(id.clone())).cloned())
    }

    #[tracing::instrument(skip(self))]
    async fn query_clients(
        &self,
        query_height: QueryHeight,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        let result = self.fetch_snapshot(query_height).await?;
        Ok(result.data.client_states.values().cloned().collect())
    }

    #[tracing::instrument(skip(self))]
    async fn query_consensus_states(
        &self,
        query_height: QueryHeight,
        request: QueryConsensusStatesRequest,
    ) -> Result<Vec<AnyConsensusStateWithHeight>, Error> {
        let result = self.fetch_snapshot(query_height).await?;

        let consensus_states = result
            .data
            .consensus_states
            .get(&request.client_id)
            .cloned()
            .unwrap_or_default();

        Ok(consensus_states)
    }

    #[tracing::instrument(skip(self))]
    async fn query_consensus_state(
        &self,
        request: QueryConsensusStateRequest,
    ) -> Result<AnyConsensusState, Error> {
        let result = self.fetch_snapshot(request.query_height).await?;

        let consensus_state = result
            .data
            .consensus_states
            .get(&request.client_id)
            .and_then(|cs| cs.iter().find(|cs| cs.height == request.consensus_height))
            .cloned()
            .ok_or_else(|| {
                // TODO(ibcnode): Use other error type
                PsqlError::consensus_state_not_found(request.client_id, request.consensus_height)
            })?;

        Ok(consensus_state.consensus_state)
    }

    #[tracing::instrument(skip(self))]
    async fn query_client_state(
        &self,
        request: QueryClientStateRequest,
    ) -> Result<AnyClientState, Error> {
        let snapshot = self.fetch_snapshot(request.height).await?;

        let client_state = snapshot
            .data
            .client_states
            .get(&request.client_id)
            .cloned()
            .ok_or_else(|| {
                // TODO(ibcnode): Use other error type
                PsqlError::client_state_not_found(request.client_id, request.height)
            })?;

        Ok(client_state.client_state)
    }

    #[tracing::instrument(skip(self))]
    async fn query_sent_packets(
        &self,
        query_height: QueryHeight,
    ) -> Result<(Height, Vec<SendPacket>), Error> {
        let result = self.fetch_snapshot(query_height).await?;

        Ok((
            result.data.app_status.height,
            result.data.pending_sent_packets.values().cloned().collect(),
        ))
    }

    #[tracing::instrument(skip(self))]
    async fn query_sent_packet(
        &self,
        query_height: QueryHeight,
        packet_id: &PacketId,
    ) -> Result<Option<SendPacket>, Error> {
        let result = self.fetch_snapshot(query_height).await?;
        let packet = result.data.pending_sent_packets.get(packet_id).cloned();
        Ok(packet)
    }
}
