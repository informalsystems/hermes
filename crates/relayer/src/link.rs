use ibc_relayer_types::core::{
    ics03_connection::connection::State as ConnectionState,
    ics04_channel::channel::State as ChannelState,
    ics04_channel::channel::UpgradeState,
    ics04_channel::packet::Sequence,
    ics24_host::identifier::{ChannelId, PortChannelId, PortId},
};
use tracing::info;

use crate::chain::counterparty::check_channel_counterparty;
use crate::chain::{handle::ChainHandle, requests::IncludeProof};
use crate::channel::{Channel, ChannelSide};
use crate::link::error::LinkError;
use crate::util::multihop::build_hops_from_connection_ids;
use crate::{
    chain::requests::{QueryChannelRequest, QueryHeight},
    config::types::ics20_field_size_limit::Ics20FieldSizeLimit,
};

pub mod cli;
pub mod error;
pub mod operational_data;
pub mod packet_events;

mod pending;
mod relay_path;
mod relay_sender;
mod relay_summary;
mod tx_hashes;

use tx_hashes::TxHashes;

// Re-export the telemetries summary
pub use relay_summary::RelaySummary;

pub use relay_path::{RelayPath, Resubmit};

#[derive(Clone, Debug)]
pub struct LinkParameters {
    pub src_port_id: PortId,
    pub src_channel_id: ChannelId,
    pub max_memo_size: Ics20FieldSizeLimit,
    pub max_receiver_size: Ics20FieldSizeLimit,
    pub exclude_src_sequences: Vec<Sequence>,
}

pub struct Link<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub a_to_b: RelayPath<ChainA, ChainB>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> Link<ChainA, ChainB> {
    pub fn new(
        channel: Channel<ChainA, ChainB>,
        with_tx_confirmation: bool,
        link_parameters: LinkParameters,
    ) -> Result<Self, LinkError> {
        Ok(Self {
            a_to_b: RelayPath::new(channel, with_tx_confirmation, link_parameters)?,
        })
    }

    pub fn new_from_opts(
        a_chain: ChainA,
        b_chain: ChainB,
        opts: LinkParameters,
        with_tx_confirmation: bool,
        auto_register_counterparty_payee: bool,
    ) -> Result<Link<ChainA, ChainB>, LinkError> {
        // Check that the packet's channel on source chain is Open
        let a_channel_id = &opts.src_channel_id;
        let a_port_id = &opts.src_port_id;
        let (a_channel, _) = a_chain
            .query_channel(
                QueryChannelRequest {
                    port_id: opts.src_port_id.clone(),
                    channel_id: opts.src_channel_id.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map_err(|e| {
                LinkError::channel_not_found(
                    a_port_id.clone(),
                    a_channel_id.clone(),
                    a_chain.id(),
                    e,
                )
            })?;

        if !a_channel.state_matches(&ChannelState::Open(UpgradeState::NotUpgrading))
            && !a_channel.state_matches(&ChannelState::Open(UpgradeState::Upgrading))
            && !a_channel.state_matches(&ChannelState::Flushing)
            && !a_channel.state_matches(&ChannelState::FlushComplete)
            && !a_channel.state_matches(&ChannelState::Closed)
        {
            return Err(LinkError::invalid_channel_state(
                a_channel_id.clone(),
                a_chain.id(),
            ));
        }

        let b_channel_id = a_channel
            .counterparty()
            .channel_id()
            .ok_or_else(|| LinkError::counterparty_channel_not_found(a_channel_id.clone()))?;

        let b_port_id = a_channel.counterparty().port_id.clone();

        let (b_channel, _) = b_chain
            .query_channel(
                QueryChannelRequest {
                    port_id: b_port_id.clone(),
                    channel_id: b_channel_id.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map_err(|e| {
                LinkError::channel_not_found(
                    b_port_id.clone(),
                    b_channel_id.clone(),
                    b_chain.id(),
                    e,
                )
            })?;

        if a_channel.connection_hops().is_empty() {
            return Err(LinkError::no_connection_hops(
                a_channel_id.clone(),
                a_chain.id(),
            ));
        }

        if b_channel.connection_hops().is_empty() {
            return Err(LinkError::no_connection_hops(
                b_channel_id.clone(),
                b_chain.id(),
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

        // Build connection hops and query all the connections along the channel path
        let a_side_hops = build_hops_from_connection_ids(&a_chain, a_channel.connection_hops())
            .map_err(LinkError::relayer)?;

        let b_side_hops = build_hops_from_connection_ids(&b_chain, b_channel.connection_hops())
            .map_err(LinkError::relayer)?;

        // Ensure all connections along the channel path are in the Open state
        for connection_hop in a_side_hops.hops_as_slice() {
            if !connection_hop
                .connection()
                .state_matches(&ConnectionState::Open)
            {
                return Err(LinkError::channel_not_opened(
                    a_channel_id.clone(),
                    a_chain.id(),
                ));
            }
        }

        let a_connection = a_side_hops
            .hops_as_slice()
            .first()
            .ok_or_else(|| LinkError::no_connection_hops(a_channel_id.clone(), a_chain.id()))?
            .clone();

        let b_connection = b_side_hops
            .hops_as_slice()
            .first()
            .ok_or_else(|| LinkError::no_connection_hops(b_channel_id.clone(), b_chain.id()))?
            .clone();

        let channel = Channel {
            ordering: a_channel.ordering,
            a_side: ChannelSide::new(
                a_chain.clone(),
                a_connection.connection().client_id().clone(),
                a_connection.connection_id().clone(),
                Some(a_side_hops),
                opts.src_port_id.clone(),
                Some(opts.src_channel_id.clone()),
                None,
            ),
            b_side: ChannelSide::new(
                b_chain.clone(),
                b_connection.connection().client_id().clone(),
                b_connection.connection_id().clone(),
                Some(b_side_hops),
                a_channel.counterparty().port_id.clone(),
                Some(b_channel_id.clone()),
                None,
            ),
            connection_delay: a_connection.connection().delay_period(),
        };

        if auto_register_counterparty_payee && a_channel.version.supports_fee() {
            let address_a = a_chain.get_signer().map_err(LinkError::relayer)?;

            info!(
                "auto registering counterparty payee on chain {} as {} on chain {}",
                b_chain.id(),
                address_a,
                a_chain.id()
            );

            b_chain
                .maybe_register_counterparty_payee(b_channel_id.clone(), b_port_id, address_a)
                .map_err(LinkError::relayer)?;
        }

        Link::new(channel, with_tx_confirmation, opts)
    }
}
