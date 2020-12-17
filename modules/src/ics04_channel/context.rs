//! ICS4 (channel) context. The two traits `ConnectionReader` and `ConnectionKeeper` define
//! the interface that any host chain must implement to be able to process any `ChannelMsg`.
//! TODO make "ADR 004: IBC protocol implementation" for more details.
//!
//use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics04_channel::channel::{ChannelEnd, State};
use crate::ics04_channel::error::Error;
use crate::ics04_channel::handler::ChannelResult;
use crate::ics04_channel::version::{get_compatible_versions, pick_version};
//use crate::ics23_commitment::commitment::CommitmentPrefix;
use crate::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
//use crate::Height;

/// A context supplying all the necessary read-only dependencies for processing any `ConnectionMsg`.
pub trait ChannelReader {
    /// Returns the ChannelEnd for the given identifier `chan_id`.
    fn channel_end(&self, port_channel_id: &(PortId, ChannelId)) -> Option<ChannelEnd>;

    /// Returns the ConnectionState for the given identifier `connection_id`.
    fn connection_state(&self, connection_id: &ConnectionId) -> Option<ConnectionEnd>;

    /// Function required by ICS 04. Returns the list of all possible versions that the channels handshake protocol supports.
    fn get_compatible_versions(&self) -> Vec<String> {
        get_compatible_versions()
    }

    /// Function required by ICS 04. Returns one version out of the supplied list of versions, which the channel handshake protocol prefers.
    fn pick_version(
        &self,
        supported_versions: Vec<String>,
        counterparty_candidate_versions: Vec<String>,
    ) -> Result<String, Error> {
        pick_version(supported_versions, counterparty_candidate_versions)
    }
}

/// A context supplying all the necessary write-only dependencies (i.e., storage writing facility)
/// for processing any `ConnectionMsg`.
pub trait ChannelKeeper {
    fn store_channel_result(&mut self, result: ChannelResult) -> Result<(), Error> {
        match result.channel_end.state() {
            State::Init => {
                self.store_channel(
                    &(result.port_id.clone(), result.channel_id.clone()),
                    &result.channel_end,
                )?;

                self.store_nextsequence_send(
                    &(result.port_id.clone(), result.channel_id.clone()),
                    1,
                )?;

                self.store_nextsequence_recv(
                    &(result.port_id.clone(), result.channel_id.clone()),
                    1,
                )?;

                self.store_nextsequence_ack(
                    &(result.port_id.clone(), result.channel_id.clone()),
                    1,
                )?;
            }
            State::TryOpen => {
                self.store_channel(&(result.port_id, result.channel_id), &result.channel_end)?;
                // TODOIf this is the first time the handler processed this channel, associate the
                // channel end to its client identifier.
                // self.store_channel_to_connection(
                //     &(result.port_id,result.channel_id),
                //     &result.... ,
                // )?;
            }
            _ => {
                self.store_channel(&(result.port_id, result.channel_id), &result.channel_end)?;
            }
        }
        Ok(())
    }

    /// Stores the given connection_end at a path associated with the connection_id.
    fn store_channel(
        &mut self,
        port_channel_id: &(PortId, ChannelId),
        channel_end: &ChannelEnd,
    ) -> Result<(), Error>;

    fn store_nextsequence_send(
        &mut self,
        port_channel_id: &(PortId, ChannelId),
        seq: u64,
    ) -> Result<(), Error>;

    fn store_nextsequence_recv(
        &mut self,
        port_channel_id: &(PortId, ChannelId),
        seq: u64,
    ) -> Result<(), Error>;

    fn store_nextsequence_ack(
        &mut self,
        port_channel_id: &(PortId, ChannelId),
        seq: u64,
    ) -> Result<(), Error>;
}
