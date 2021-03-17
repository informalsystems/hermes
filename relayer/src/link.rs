use std::thread;
use std::time::Duration;

use ibc::{
    events::IbcEvent,
    ics03_connection::connection::State as ConnectionState,
    ics04_channel::channel::State as ChannelState,
    ics24_host::identifier::{ChannelId, PortId},
    Height,
};

use crate::chain::handle::ChainHandle;
use crate::channel::{Channel, ChannelSide};
use crate::link::error::LinkError;
use crate::link::relay_path::RelayPath;

mod error;
mod relay_path;

#[derive(Clone, Debug)]
pub struct LinkParameters {
    pub src_port_id: PortId,
    pub src_channel_id: ChannelId,
}

pub struct Link {
    pub a_to_b: RelayPath,
    pub b_to_a: RelayPath,
}

impl Link {
    pub fn new(channel: Channel) -> Self {
        let a_chain = channel.src_chain();
        let b_chain = channel.dst_chain();
        let flipped = channel.flipped();

        Self {
            a_to_b: RelayPath::new(a_chain.clone(), b_chain.clone(), channel),
            b_to_a: RelayPath::new(b_chain, a_chain, flipped),
        }
    }

    pub fn relay(&mut self) -> Result<(), LinkError> {
        println!("relaying packets on {:#?}", self.a_to_b.channel());

        let events_a = self.a_to_b.src_chain().subscribe()?;
        let events_b = self.b_to_a.src_chain().subscribe()?;

        loop {
            if self.is_closed()? {
                println!("channel is closed, exiting");
                return Ok(());
            }

            if let Ok(batch) = events_a.try_recv() {
                self.a_to_b.relay_from_events(batch.unwrap_or_clone())?;
            }

            if let Ok(batch) = events_b.try_recv() {
                self.b_to_a.relay_from_events(batch.unwrap_or_clone())?;
            }

            // TODO - select over the two subscriptions
            thread::sleep(Duration::from_millis(100))
        }
    }

    fn is_closed(&self) -> Result<bool, LinkError> {
        let a_channel = self
            .a_to_b
            .src_chain()
            .query_channel(
                self.a_to_b.src_port_id(),
                self.a_to_b.src_channel_id(),
                Height::default(),
            )
            .map_err(|e| {
                LinkError::Failed(format!(
                    "channel {} does not exist on chain {}; context={}",
                    self.a_to_b.src_channel_id(),
                    self.a_to_b.src_chain().id(),
                    e
                ))
            })?;

        let b_channel = self
            .a_to_b
            .dst_chain()
            .query_channel(
                self.a_to_b.dst_port_id(),
                self.a_to_b.dst_channel_id(),
                Height::default(),
            )
            .map_err(|e| {
                LinkError::Failed(format!(
                    "channel {} does not exist on chain {}; context={}",
                    self.a_to_b.dst_channel_id(),
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
            return Err(LinkError::Failed(format!(
                "channel {} on chain {} not in open or close state when packets and timeouts can be relayed",
                a_channel_id.clone(),
                a_chain.id()
            )));
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
                opts.src_channel_id.clone(),
            ),
            b_side: ChannelSide::new(
                b_chain,
                a_connection.counterparty().client_id().clone(),
                a_connection.counterparty().connection_id().unwrap().clone(),
                a_channel.counterparty().port_id.clone(),
                b_channel_id,
            ),
        };

        Ok(Link::new(channel))
    }

    pub fn build_and_send_recv_packet_messages(&mut self) -> Result<Vec<IbcEvent>, LinkError> {
        self.a_to_b.build_recv_packet_and_timeout_msgs()?;
        let (mut dst_res, mut src_res) = self.a_to_b.send_update_client_and_msgs()?;
        dst_res.append(&mut src_res);
        Ok(dst_res)
    }

    pub fn build_and_send_ack_packet_messages(&mut self) -> Result<Vec<IbcEvent>, LinkError> {
        self.a_to_b.build_packet_ack_msgs()?;
        let (mut dst_res, mut src_res) = self.a_to_b.send_update_client_and_msgs()?;
        dst_res.append(&mut src_res);
        Ok(dst_res)
    }
}
