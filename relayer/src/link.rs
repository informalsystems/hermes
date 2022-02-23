use ibc::{
    core::{
        ics03_connection::connection::State as ConnectionState,
        ics04_channel::channel::State as ChannelState,
        ics24_host::identifier::{ChannelId, PortChannelId, PortId},
    },
    events::IbcEvent,
    Height,
};
use tracing::error_span;

use crate::chain::counterparty::check_channel_counterparty;
use crate::chain::handle::ChainHandle;
use crate::channel::{Channel, ChannelSide};
use crate::link::error::LinkError;
use crate::link::relay_path::RelayPath;

pub mod error;
pub mod operational_data;
mod pending;
mod relay_path;
mod relay_sender;
mod relay_summary;
mod tx_hashes;
use tx_hashes::TxHashes;

// Re-export the telemetries summary
pub use relay_summary::RelaySummary;

#[derive(Clone, Debug)]
pub struct LinkParameters {
    pub src_port_id: PortId,
    pub src_channel_id: ChannelId,
}

pub struct Link<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub a_to_b: RelayPath<ChainA, ChainB>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> Link<ChainA, ChainB> {
    pub fn new(
        channel: Channel<ChainA, ChainB>,
        with_tx_confirmation: bool,
    ) -> Result<Self, LinkError> {
        Ok(Self {
            a_to_b: RelayPath::new(channel, with_tx_confirmation)?,
        })
    }

    pub fn is_closed(&self) -> Result<bool, LinkError> {
        let a_channel_id = self.a_to_b.src_channel_id();

        let a_channel = self
            .a_to_b
            .src_chain()
            .query_channel(self.a_to_b.src_port_id(), a_channel_id, Height::default())
            .map_err(|e| {
                LinkError::channel_not_found(
                    self.a_to_b.src_port_id().clone(),
                    a_channel_id.clone(),
                    self.a_to_b.src_chain().id(),
                    e,
                )
            })?;

        let b_channel_id = self.a_to_b.dst_channel_id();

        let b_channel = self
            .a_to_b
            .dst_chain()
            .query_channel(self.a_to_b.dst_port_id(), b_channel_id, Height::default())
            .map_err(|e| {
                LinkError::channel_not_found(
                    self.a_to_b.dst_port_id().clone(),
                    b_channel_id.clone(),
                    self.a_to_b.dst_chain().id(),
                    e,
                )
            })?;

        if a_channel.state_matches(&ChannelState::Closed)
            && b_channel.state_matches(&ChannelState::Closed)
        {
            Ok(true)
        } else {
            Ok(false)
        }
    }

    pub fn new_from_opts(
        a_chain: ChainA,
        b_chain: ChainB,
        opts: LinkParameters,
        with_tx_confirmation: bool,
    ) -> Result<Link<ChainA, ChainB>, LinkError> {
        // Check that the packet's channel on source chain is Open
        let a_channel_id = &opts.src_channel_id;
        let a_port_id = &opts.src_port_id;
        let a_channel = a_chain
            .query_channel(a_port_id, a_channel_id, Height::default())
            .map_err(|e| {
                LinkError::channel_not_found(
                    a_port_id.clone(),
                    a_channel_id.clone(),
                    a_chain.id(),
                    e,
                )
            })?;

        if !a_channel.state_matches(&ChannelState::Open)
            && !a_channel.state_matches(&ChannelState::Closed)
        {
            return Err(LinkError::invalid_channel_state(
                a_channel_id.clone(),
                a_chain.id(),
            ));
        }

        let b_channel_id = a_channel
            .counterparty()
            .channel_id
            .clone()
            .ok_or_else(|| LinkError::counterparty_channel_not_found(a_channel_id.clone()))?;

        if a_channel.connection_hops().is_empty() {
            return Err(LinkError::no_connection_hop(
                a_channel_id.clone(),
                a_chain.id(),
            ));
        }

        // Check that the counterparty details on the destination chain matches the source chain
        check_channel_counterparty(
            b_chain.clone(),
            &PortChannelId {
                channel_id: b_channel_id.clone(),
                port_id: a_channel.counterparty().port_id.clone(),
            },
            &PortChannelId {
                channel_id: a_channel_id.clone(),
                port_id: opts.src_port_id.clone(),
            },
        )
        .map_err(LinkError::initialization)?;

        // Check the underlying connection
        let a_connection_id = a_channel.connection_hops()[0].clone();
        let a_connection = a_chain
            .query_connection(&a_connection_id, Height::zero())
            .map_err(LinkError::relayer)?;

        if !a_connection.state_matches(&ConnectionState::Open) {
            return Err(LinkError::channel_not_opened(
                a_channel_id.clone(),
                a_chain.id(),
            ));
        }

        let channel = Channel {
            ordering: a_channel.ordering,
            a_side: ChannelSide::new(
                a_chain,
                a_connection.client_id().clone(),
                a_connection_id,
                opts.src_port_id.clone(),
                Some(opts.src_channel_id.clone()),
                None,
            ),
            b_side: ChannelSide::new(
                b_chain,
                a_connection.counterparty().client_id().clone(),
                a_connection.counterparty().connection_id().unwrap().clone(),
                a_channel.counterparty().port_id.clone(),
                Some(b_channel_id),
                None,
            ),
            connection_delay: a_connection.delay_period(),
        };

        Link::new(channel, with_tx_confirmation)
    }

    /// Constructs a link around the channel that is reverse to the channel
    /// in this link.
    pub fn reverse(&self, with_tx_confirmation: bool) -> Result<Link<ChainB, ChainA>, LinkError> {
        let opts = LinkParameters {
            src_port_id: self.a_to_b.dst_port_id().clone(),
            src_channel_id: self.a_to_b.dst_channel_id().clone(),
        };
        let chain_b = self.a_to_b.dst_chain().clone();
        let chain_a = self.a_to_b.src_chain().clone();

        // Some of the checks and initializations may be redundant;
        // going slowly, but reliably.
        Link::new_from_opts(chain_b, chain_a, opts, with_tx_confirmation)
    }

    /// Implements the `packet-recv` CLI
    pub fn build_and_send_recv_packet_messages(&self) -> Result<Vec<IbcEvent>, LinkError> {
        let _span = error_span!(
            "PacketRecvCmd",
            src_chain = %self.a_to_b.src_chain().id(),
            src_port = %self.a_to_b.src_port_id(),
            src_channel = %self.a_to_b.src_channel_id(),
            dst_chain = %self.a_to_b.dst_chain().id(),
        )
        .entered();

        self.a_to_b.build_recv_packet_and_timeout_msgs(None)?;

        let mut results = vec![];

        // Block waiting for all of the scheduled data (until `None` is returned)
        while let Some(odata) = self.a_to_b.fetch_scheduled_operational_data() {
            let mut last_res = self
                .a_to_b
                .relay_from_operational_data::<relay_sender::SyncSender>(odata)?;
            results.append(&mut last_res.events);
        }

        Ok(results)
    }

    /// Implements the `packet-ack` CLI
    pub fn build_and_send_ack_packet_messages(&self) -> Result<Vec<IbcEvent>, LinkError> {
        let _span = error_span!(
            "PacketAckCmd",
            src_chain = %self.a_to_b.src_chain().id(),
            src_port = %self.a_to_b.src_port_id(),
            src_channel = %self.a_to_b.src_channel_id(),
            dst_chain = %self.a_to_b.dst_chain().id(),
        )
        .entered();

        self.a_to_b.build_packet_ack_msgs(None)?;

        let mut results = vec![];

        // Block waiting for all of the scheduled data
        while let Some(odata) = self.a_to_b.fetch_scheduled_operational_data() {
            let mut last_res = self
                .a_to_b
                .relay_from_operational_data::<relay_sender::SyncSender>(odata)?;
            results.append(&mut last_res.events);
        }

        Ok(results)
    }
}
