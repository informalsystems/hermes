use prost_types::Any;

use ibc_proto::ibc::core::client::v1::MsgUpdateClient as RawMsgUpdateClient;
use ibc_proto::ibc::core::channel::v1::MsgChannelOpenAck as RawMsgChannelOpenAck;
use ibc_proto::ibc::core::channel::v1::MsgChannelOpenConfirm as RawMsgChannelOpenConfirm;
use ibc_proto::ibc::core::channel::v1::MsgChannelOpenInit as RawMsgChannelOpenInit;
use ibc_proto::ibc::core::channel::v1::MsgChannelOpenTry as RawMsgChannelOpenTry;

use ibc::Height as ICSHeight;
use ibc::ics04_channel::msgs::chan_open_init::MsgChannelOpenInit;
use ibc::ics04_channel::channel::{Counterparty, ChannelEnd, Order, State};
use ibc::ics24_host::identifier::{ClientId, ConnectionId, PortId, ChannelId};
use ibc::tx_msg::Msg;

use crate::config::ChainConfig;
use crate::chain::{CosmosSDKChain, Chain};
use crate::error::{Error, Kind};

/// Enumeration of proof carrying ICS4 message, helper for relayer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChannelMsgType {
    ChanTry,
    ChanAck,
    ChanConfirm,
}

#[derive(Clone, Debug)]
pub struct ChannelOpenInitOptions {
    pub dest_chain_config: ChainConfig,
    pub src_chain_config: ChainConfig,
    pub dest_connection_id: ConnectionId,
    pub dest_port_id: PortId,
    pub src_port_id: PortId,
    pub dest_channel_id: ChannelId,
    pub src_channel_id: Option<ChannelId>,
    pub ordering: Order,
    pub signer_seed: String,
}

pub fn build_chan_init(
    dest_chain: &mut CosmosSDKChain,
    src_chain: &CosmosSDKChain,
    opts: &ChannelOpenInitOptions,
) -> Result<Vec<Any>, Error> {
    // Check that the destination chain will accept the message, i.e. it does not have the channel
    if dest_chain
        .query_channel(&opts.dest_port_id, &opts.dest_channel_id, ICSHeight::default())
        .is_ok()
    {
        return Err(Kind::ChanOpenInit(
            opts.dest_channel_id.clone(),
            "channel already exist".into(),
        )
            .into());
    }

    // Get the signer from key seed file
    let (_, signer) = dest_chain.key_and_signer(&opts.signer_seed)?;

    let prefix = src_chain.query_commitment_prefix()?;

    let counterparty = Counterparty::new(
        opts.src_port_id.clone(),
        opts.src_channel_id.clone(),
    );

    let channel = ChannelEnd::new(
        State::Init,
        opts.ordering,
        counterparty,
        vec![opts.dest_connection_id.clone()],
        dest_chain.module_versions(&opts.dest_port_id),
    );

    // Build the domain type message
    let new_msg = MsgChannelOpenInit {
        port_id: opts.dest_port_id.clone(),
        channel_id: opts.dest_channel_id.clone(),
        channel,
        signer
    };

    Ok(vec![new_msg.to_any::<RawMsgChannelOpenInit>()])
}

pub fn build_chan_init_and_send(opts: &ChannelOpenInitOptions) -> Result<String, Error> {
    // Get the source and destination chains.
    let src_chain = &CosmosSDKChain::from_config(opts.clone().src_chain_config)?;
    let dest_chain = &mut CosmosSDKChain::from_config(opts.clone().dest_chain_config)?;

    let new_msgs = build_chan_init(dest_chain, src_chain, opts)?;
    let (key, _) = dest_chain.key_and_signer(&opts.signer_seed)?;

    Ok(dest_chain.send(new_msgs, key, "".to_string(), 0)?)
}

#[derive(Clone, Debug)]
pub struct ChannelOpenTryOptions {
    pub dest_chain_config: ChainConfig,
    pub src_chain_config: ChainConfig,
    pub dest_port_id: PortId,
    pub src_port_id: PortId,
    pub dest_channel_id: ChannelId,
    pub src_channel_id: ChannelId,
    pub dest_connection_id: ConnectionId,
    pub ordering: Order,
    pub signer_seed: String,
}

pub fn build_chan_try(
    dest_chain: &mut CosmosSDKChain,
    src_chain: &CosmosSDKChain,
    opts: &ChannelOpenTryOptions,
) -> Result<Vec<Any>, Error> {
    // Check that the destination chain will accept the message, i.e. it does not have the channel
    if dest_chain
        .query_channel(&opts.dest_port_id, &opts.dest_channel_id, ICSHeight::default())
        .is_ok()
    {
        return Err(Kind::ChanOpenInit(
            opts.dest_channel_id.clone(),
            "channel already exist".into(),
        )
            .into());
    }

    // Get the signer from key seed file
    let (_, signer) = dest_chain.key_and_signer(&opts.signer_seed)?;

    let prefix = src_chain.query_commitment_prefix()?;

    let counterparty = Counterparty::new(
        opts.src_port_id.clone(),
        Some(opts.src_channel_id.clone()),
    );

    let channel = ChannelEnd::new(
        State::Init,
        opts.ordering,
        counterparty,
        vec![opts.dest_connection_id.clone()],
        dest_chain.module_versions(&opts.dest_port_id),
    );

    // Build the domain type message
    let new_msg = MsgChannelOpenInit {
        port_id: opts.dest_port_id.clone(),
        channel_id: opts.dest_channel_id.clone(),
        channel,
        signer
    };

    Ok(vec![new_msg.to_any::<RawMsgChannelOpenInit>()])
}

pub fn build_chan_try_and_send(opts: &ChannelOpenTryOptions) -> Result<String, Error> {
    // Get the source and destination chains.
    let src_chain = &CosmosSDKChain::from_config(opts.clone().src_chain_config)?;
    let dest_chain = &mut CosmosSDKChain::from_config(opts.clone().dest_chain_config)?;

    let new_msgs = build_chan_try(dest_chain, src_chain, opts)?;
    let (key, _) = dest_chain.key_and_signer(&opts.signer_seed)?;

    Ok(dest_chain.send(new_msgs, key, "".to_string(), 0)?)
}