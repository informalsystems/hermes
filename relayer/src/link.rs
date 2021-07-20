use ibc::{
    events::IbcEvent,
    ics03_connection::connection::State as ConnectionState,
    ics04_channel::channel::State as ChannelState,
    ics24_host::identifier::{ChannelId, PortChannelId, PortId},
    Height,
};

use crate::chain::counterparty::check_channel_counterparty;
use crate::chain::handle::ChainHandle;
use crate::channel::{Channel, ChannelSide};
use crate::link::error::LinkError;
use crate::link::relay_path::RelayPath;

mod error;
mod operational_data;
mod relay_path;
mod relay_sender;
mod relay_summary;

// Re-export the telemetries summary
pub use relay_summary::RelaySummary;

#[derive(Clone, Debug)]
pub struct LinkParameters {
    pub src_port_id: PortId,
    pub src_channel_id: ChannelId,
}

// TODO: Refactor this, so we avoid calling `link.a_to_b`.
pub struct Link {
    pub a_to_b: RelayPath,
}

impl Link {
    pub fn new(channel: Channel) -> Self {
        Self {
            a_to_b: RelayPath::new(channel),
        }
    }

    pub fn is_closed(&self) -> Result<bool, LinkError> {
        let a_channel_id = self.a_to_b.src_channel_id()?;

        let a_channel = self
            .a_to_b
            .src_chain()
            .query_channel(self.a_to_b.src_port_id(), a_channel_id, Height::default())
            .map_err(|e| {
                LinkError::Failed(format!(
                    "channel {} does not exist on chain {}; context={}",
                    a_channel_id,
                    self.a_to_b.src_chain().id(),
                    e
                ))
            })?;

        let b_channel_id = self.a_to_b.dst_channel_id()?;

        let b_channel = self
            .a_to_b
            .dst_chain()
            .query_channel(self.a_to_b.dst_port_id(), b_channel_id, Height::default())
            .map_err(|e| {
                LinkError::Failed(format!(
                    "channel {} does not exist on chain {}; context={}",
                    b_channel_id,
                    self.a_to_b.dst_chain().id(),
                    e
                ))
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
        a_chain: Box<dyn ChainHandle>,
        b_chain: Box<dyn ChainHandle>,
        opts: LinkParameters,
    ) -> Result<Link, LinkError> {
        // Check that the packet's channel on source chain is Open
        let a_channel_id = &opts.src_channel_id;
        let a_channel = a_chain
            .query_channel(&opts.src_port_id, a_channel_id, Height::default())
            .map_err(|e| {
                LinkError::Failed(format!(
                    "channel {} does not exist on chain {}; context={}",
                    a_channel_id.clone(),
                    a_chain.id(),
                    e
                ))
            })?;

        if !a_channel.state_matches(&ChannelState::Open)
            && !a_channel.state_matches(&ChannelState::Closed)
        {
            return Err(LinkError::ConstructorFailed(
                a_channel_id.clone(),
                opts.src_port_id,
                a_chain.id(),
            ));
        }

        let b_channel_id = a_channel.counterparty().channel_id.clone().ok_or_else(|| {
            LinkError::Failed(format!(
                "counterparty channel id not found for {}",
                a_channel_id
            ))
        })?;

        if a_channel.connection_hops().is_empty() {
            return Err(LinkError::Failed(format!(
                "channel {} on chain {} has no connection hops",
                a_channel_id.clone(),
                a_chain.id()
            )));
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
        .map_err(LinkError::Initialization)?;

        // Check the underlying connection
        let a_connection_id = a_channel.connection_hops()[0].clone();
        let a_connection = a_chain.query_connection(&a_connection_id, Height::zero())?;

        if !a_connection.state_matches(&ConnectionState::Open) {
            return Err(LinkError::Failed(format!(
                "connection for channel {} on chain {} not in open state",
                a_channel_id.clone(),
                a_chain.id()
            )));
        }

        let channel = Channel {
            ordering: Default::default(),
            a_side: ChannelSide::new(
                a_chain,
                a_connection.client_id().clone(),
                a_connection_id,
                opts.src_port_id.clone(),
                Some(opts.src_channel_id.clone()),
            ),
            b_side: ChannelSide::new(
                b_chain,
                a_connection.counterparty().client_id().clone(),
                a_connection.counterparty().connection_id().unwrap().clone(),
                a_channel.counterparty().port_id.clone(),
                Some(b_channel_id),
            ),
            connection_delay: a_connection.delay_period(),
            version: None,
        };

        Ok(Link::new(channel))
    }

    /// Implements the `packet-recv` CLI
    pub fn build_and_send_recv_packet_messages(&mut self) -> Result<Vec<IbcEvent>, LinkError> {
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
    pub fn build_and_send_ack_packet_messages(&mut self) -> Result<Vec<IbcEvent>, LinkError> {
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
