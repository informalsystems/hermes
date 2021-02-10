//! ICS4 (channel) context. The two traits `ChannelReader ` and `ChannelKeeper` define
//! the interface that any host chain must implement to be able to process any `ChannelMsg`.
//!
use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics04_channel::channel::ChannelEnd;
use crate::ics04_channel::channel::State;
use crate::ics04_channel::error::Error;
use crate::ics04_channel::handler::ChannelResult;
use crate::ics05_port::capabilities::Capability;
use crate::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use crate::Height;

/// A context supplying all the necessary read-only dependencies for processing any `ChannelMsg`.
pub trait ChannelReader {
    /// Returns the ChannelEnd for the given `port_id` and `chan_id`.
    fn channel_end(&self, port_channel_id: &(PortId, ChannelId)) -> Option<ChannelEnd>;

    /// Returns the ConnectionState for the given identifier `connection_id`.
    fn connection_end(&self, connection_id: &ConnectionId) -> Option<ConnectionEnd>;

    fn connection_channels(&self, cid: &ConnectionId) -> Option<Vec<(PortId, ChannelId)>>;

    fn channel_client_state(&self, port_channel_id: &(PortId, ChannelId))
        -> Option<AnyClientState>;

    fn channel_client_consensus_state(
        &self,
        port_channel_id: &(PortId, ChannelId),
        height: Height,
    ) -> Option<AnyConsensusState>;

    fn authenticated_capability(&self, port_id: &PortId) -> Result<Capability, Error>;

    /// Returns a counter on the number of channel ids have been created thus far.
    /// The value of this counter should increase only via method
    /// `ChannelKeeper::increase_channel_counter`.
    fn channel_counter(&self) -> u64;
}

/// A context supplying all the necessary write-only dependencies (i.e., storage writing facility)
/// for processing any `ChannelMsg`.
pub trait ChannelKeeper {
    fn store_channel_result(&mut self, result: ChannelResult) -> Result<(), Error> {
        match result.channel_end.state() {
            // This is the first time the handler processed this channel, with `MsgChannelOpenInit`.
            State::Init => {
                self.store_channel(
                    &(result.port_id.clone(), result.channel_id.clone()),
                    &result.channel_end,
                )?;

                // Associate also the channel end to its connection.
                self.store_connection_channels(
                    &result.channel_end.connection_hops()[0].clone(),
                    &(result.port_id.clone(), result.channel_id.clone()),
                )?;

                // Initialize send, recv, and ack sequence numbers.
                self.store_next_sequence_send(
                    &(result.port_id.clone(), result.channel_id.clone()),
                    1,
                )?;
                self.store_next_sequence_recv(
                    &(result.port_id.clone(), result.channel_id.clone()),
                    1,
                )?;
                self.store_next_sequence_ack(&(result.port_id, result.channel_id), 1)?;

                // Bump the channel counter.
                self.increase_channel_counter();
            }
            // The handler processed this channel & some modifications occurred, store the new end.
            _ => {
                self.store_channel(
                    &(result.port_id.clone(), result.channel_id.clone()),
                    &result.channel_end,
                )?;

                // There was no previous_channel_id, which means we generated one.
                if matches!(result.previous_channel_id, None) {
                    self.increase_channel_counter();
                }
            }
        }
        Ok(())
    }

    fn store_connection_channels(
        &mut self,
        conn_id: &ConnectionId,
        port_channel_id: &(PortId, ChannelId),
    ) -> Result<(), Error>;

    /// Stores the given channel_end at a path associated with the port_id and channel_id.
    fn store_channel(
        &mut self,
        port_channel_id: &(PortId, ChannelId),
        channel_end: &ChannelEnd,
    ) -> Result<(), Error>;

    fn store_next_sequence_send(
        &mut self,
        port_channel_id: &(PortId, ChannelId),
        seq: u64,
    ) -> Result<(), Error>;

    fn store_next_sequence_recv(
        &mut self,
        port_channel_id: &(PortId, ChannelId),
        seq: u64,
    ) -> Result<(), Error>;

    fn store_next_sequence_ack(
        &mut self,
        port_channel_id: &(PortId, ChannelId),
        seq: u64,
    ) -> Result<(), Error>;

    /// Called upon channel identifier creation (Init or Try message processing).
    /// Increases the counter which keeps track of how many channels have been created.
    /// Should never fail.
    fn increase_channel_counter(&mut self);
}
