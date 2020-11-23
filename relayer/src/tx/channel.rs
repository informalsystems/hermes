use prost_types::Any;

use ibc_proto::ibc::core::channel::v1::MsgChannelOpenAck as RawMsgChannelOpenAck;
use ibc_proto::ibc::core::channel::v1::MsgChannelOpenConfirm as RawMsgChannelOpenConfirm;
use ibc_proto::ibc::core::channel::v1::MsgChannelOpenInit as RawMsgChannelOpenInit;
use ibc_proto::ibc::core::channel::v1::MsgChannelOpenTry as RawMsgChannelOpenTry;

use ibc::ics04_channel::channel::{ChannelEnd, Counterparty, Order, State};
use ibc::ics04_channel::msgs::chan_open_ack::MsgChannelOpenAck;
use ibc::ics04_channel::msgs::chan_open_confirm::MsgChannelOpenConfirm;
use ibc::ics04_channel::msgs::chan_open_init::MsgChannelOpenInit;
use ibc::ics04_channel::msgs::chan_open_try::MsgChannelOpenTry;
use ibc::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use ibc::tx_msg::Msg;
use ibc::Height as ICSHeight;

use crate::chain::{handle::ChainHandle, runtime::ChainRuntime};
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::tx::client::build_update_client;

/// Enumeration of proof carrying ICS4 message, helper for relayer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChannelMsgType {
    OpenTry,
    OpenAck,
    OpenConfirm,
}

#[derive(Clone, Debug)]
pub struct ChannelOpenInitOptions {
    pub dst_chain_config: ChainConfig,
    pub src_chain_config: ChainConfig,
    pub dst_connection_id: ConnectionId,
    pub dst_port_id: PortId,
    pub src_port_id: PortId,
    pub dst_channel_id: ChannelId,
    pub src_channel_id: Option<ChannelId>,
    pub ordering: Order,
}

pub fn build_chan_init(
    dst_chain: impl ChainHandle,
    _src_chain: impl ChainHandle,
    opts: &ChannelOpenInitOptions,
) -> Result<Vec<Any>, Error> {
    // Check that the destination chain will accept the message, i.e. it does not have the channel
    if dst_chain
        .query_channel(
            &opts.dst_port_id,
            &opts.dst_channel_id,
            ICSHeight::default(),
        )
        .is_ok()
    {
        return Err(Kind::ChanOpenInit(
            opts.dst_channel_id.clone(),
            "channel already exist".into(),
        )
        .into());
    }

    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    let counterparty = Counterparty::new(opts.src_port_id.clone(), opts.src_channel_id.clone());

    let channel = ChannelEnd::new(
        State::Init,
        opts.ordering,
        counterparty,
        vec![opts.dst_connection_id.clone()],
        dst_chain.module_version(&opts.dst_port_id)?,
    );

    // Build the domain type message
    let new_msg = MsgChannelOpenInit {
        port_id: opts.dst_port_id.clone(),
        channel_id: opts.dst_channel_id.clone(),
        channel,
        signer,
    };

    Ok(vec![new_msg.to_any::<RawMsgChannelOpenInit>()])
}

pub fn build_chan_init_and_send(opts: &ChannelOpenInitOptions) -> Result<String, Error> {
    // Get the source and destination chains.
    let (src_chain, _) = ChainRuntime::spawn(opts.clone().src_chain_config)?;
    let (dst_chain, _) = ChainRuntime::spawn(opts.clone().dst_chain_config)?;

    let new_msgs = build_chan_init(dst_chain.clone(), src_chain, opts)?;
    let key = dst_chain.get_key().map_err(|e| Kind::KeyBase.context(e))?;

    Ok(dst_chain.send_tx(new_msgs, key, "".to_string(), 0)?)
}

#[derive(Clone, Debug)]
pub struct ChannelOpenOptions {
    pub dst_chain_config: ChainConfig,
    pub src_chain_config: ChainConfig,
    pub dst_port_id: PortId,
    pub src_port_id: PortId,
    pub dst_channel_id: ChannelId,
    pub src_channel_id: ChannelId,
    pub dst_connection_id: ConnectionId,
    pub ordering: Order,
}

fn check_destination_channel_state(
    channel_id: ChannelId,
    existing_channel: ChannelEnd,
    expected_channel: ChannelEnd,
) -> Result<(), Error> {
    let good_connection_hops =
        existing_channel.connection_hops() == expected_channel.connection_hops();

    let good_state =
        existing_channel.state().clone() as u32 <= expected_channel.state().clone() as u32;

    let good_channel_ids = existing_channel.counterparty().channel_id().is_none()
        || existing_channel.counterparty().channel_id()
            == expected_channel.counterparty().channel_id();

    // TODO check versions

    if good_state && good_connection_hops && good_channel_ids {
        Ok(())
    } else {
        Err(Kind::ChanOpenTry(
            channel_id,
            "channel already exist in an incompatible state".into(),
        )
        .into())
    }
}

/// Retrieves the channel from destination and compares against the expected channel
/// built from the message type (`msg_type`) and options (`opts`).
/// If the expected and the destination channels are compatible, it returns the expected channel
fn validated_expected_channel(
    dst_chain: impl ChainHandle,
    _src_chain: impl ChainHandle,
    msg_type: ChannelMsgType,
    opts: &ChannelOpenOptions,
) -> Result<ChannelEnd, Error> {
    // If there is a channel present on the destination chain, it should look like this:
    let counterparty = Counterparty::new(
        opts.src_port_id.clone(),
        Option::from(opts.src_channel_id.clone()),
    );

    // The highest expected state, depends on the message type:
    let highest_state = match msg_type {
        ChannelMsgType::OpenTry => State::Init,
        ChannelMsgType::OpenAck => State::TryOpen,
        ChannelMsgType::OpenConfirm => State::TryOpen,
    };

    let dest_expected_channel = ChannelEnd::new(
        highest_state,
        opts.ordering,
        counterparty,
        vec![opts.dst_connection_id.clone()],
        dst_chain.module_version(&opts.dst_port_id)?,
    );

    // Retrieve existing channel if any
    let dest_channel = dst_chain.query_channel(
        &opts.dst_port_id,
        &opts.dst_channel_id,
        ICSHeight::default(),
    );

    // Check if a connection is expected to exist on destination chain
    if msg_type == ChannelMsgType::OpenTry {
        // TODO - check typed Err, or make query_channel return Option<ChannelEnd>
        // It is ok if there is no channel for Try Tx
        if dest_channel.is_err() {
            return Ok(dest_expected_channel);
        }
    } else {
        // A channel must exist on destination chain for Ack and Confirm Tx-es to succeed
        if dest_channel.is_err() {
            return Err(Kind::ChanOpenTry(
                opts.src_channel_id.clone(),
                "missing channel on source chain".to_string(),
            )
            .into());
        }
    }

    check_destination_channel_state(
        opts.dst_channel_id.clone(),
        dest_channel?,
        dest_expected_channel.clone(),
    )?;

    Ok(dest_expected_channel)
}

pub fn build_chan_try(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    opts: &ChannelOpenOptions,
) -> Result<Vec<Any>, Error> {
    // Check that the destination chain will accept the message, i.e. it does not have the channel
    let _dest_expected_channel = validated_expected_channel(
        dst_chain.clone(),
        src_chain.clone(),
        ChannelMsgType::OpenTry,
        opts,
    )
    .map_err(|e| {
        Kind::ChanOpenTry(
            opts.src_channel_id.clone(),
            "try options inconsistent with existing channel on destination chain".to_string(),
        )
        .context(e)
    })?;

    let src_channel = src_chain
        .query_channel(
            &opts.src_port_id,
            &opts.src_channel_id,
            ICSHeight::default(),
        )
        .map_err(|e| {
            Kind::ChanOpenTry(
                opts.dst_channel_id.clone(),
                "channel does not exist on source".into(),
            )
            .context(e)
        })?;

    // Retrieve the connection
    let dest_connection =
        dst_chain.query_connection(&opts.dst_connection_id.clone(), ICSHeight::default())?;

    let ics_target_height = src_chain.query_latest_height()?;

    // Build message to update client on destination
    let mut msgs = build_update_client(
        dst_chain.clone(),
        src_chain.clone(),
        dest_connection.client_id().clone(),
        ics_target_height,
    )?;

    let counterparty =
        Counterparty::new(opts.src_port_id.clone(), Some(opts.src_channel_id.clone()));

    let channel = ChannelEnd::new(
        State::Init,
        opts.ordering,
        counterparty,
        vec![opts.dst_connection_id.clone()],
        dst_chain.module_version(&opts.dst_port_id)?,
    );

    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    // Build the domain type message
    let new_msg = MsgChannelOpenTry {
        port_id: opts.dst_port_id.clone(),
        channel_id: opts.dst_channel_id.clone(),
        counterparty_chosen_channel_id: src_channel.counterparty().channel_id,
        channel,
        counterparty_version: src_chain.module_version(&opts.src_port_id)?,
        proofs: src_chain.build_channel_proofs(
            &opts.src_port_id,
            &opts.src_channel_id,
            ics_target_height,
        )?,
        signer,
    };

    let mut new_msgs = vec![new_msg.to_any::<RawMsgChannelOpenTry>()];

    msgs.append(&mut new_msgs);

    Ok(msgs)
}

pub fn build_chan_try_and_send(opts: &ChannelOpenOptions) -> Result<String, Error> {
    // Get the source and destination chains.
    let (src_chain, _) = ChainRuntime::spawn(opts.clone().src_chain_config)?;
    let (dst_chain, _) = ChainRuntime::spawn(opts.clone().dst_chain_config)?;

    let new_msgs = build_chan_try(dst_chain.clone(), src_chain, opts)?;
    let key = dst_chain.get_key().map_err(|e| Kind::KeyBase.context(e))?;

    Ok(dst_chain.send_tx(new_msgs, key, "".to_string(), 0)?)
}

pub fn build_chan_ack(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    opts: &ChannelOpenOptions,
) -> Result<Vec<Any>, Error> {
    // Check that the destination chain will accept the message
    let _dest_expected_channel = validated_expected_channel(
        dst_chain.clone(),
        src_chain.clone(),
        ChannelMsgType::OpenAck,
        opts,
    )
    .map_err(|e| {
        Kind::ChanOpenAck(
            opts.src_channel_id.clone(),
            "ack options inconsistent with existing channel on destination chain".to_string(),
        )
        .context(e)
    })?;

    let _src_channel = src_chain
        .query_channel(
            &opts.src_port_id,
            &opts.src_channel_id,
            ICSHeight::default(),
        )
        .map_err(|e| {
            Kind::ChanOpenAck(
                opts.dst_channel_id.clone(),
                "channel does not exist on source".into(),
            )
            .context(e)
        })?;

    // Retrieve the connection
    let dest_connection =
        dst_chain.query_connection(&opts.dst_connection_id.clone(), ICSHeight::default())?;

    let ics_target_height = src_chain.query_latest_height()?;

    // Build message to update client on destination
    let mut msgs = build_update_client(
        dst_chain.clone(),
        src_chain.clone(),
        dest_connection.client_id().clone(),
        ics_target_height,
    )?;

    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    // Build the domain type message
    let new_msg = MsgChannelOpenAck {
        port_id: opts.dst_port_id.clone(),
        channel_id: opts.dst_channel_id.clone(),
        counterparty_channel_id: opts.src_channel_id.clone(),
        counterparty_version: src_chain.module_version(&opts.dst_port_id)?,
        proofs: src_chain.build_channel_proofs(
            &opts.src_port_id,
            &opts.src_channel_id,
            ics_target_height,
        )?,
        signer,
    };

    let mut new_msgs = vec![new_msg.to_any::<RawMsgChannelOpenAck>()];

    msgs.append(&mut new_msgs);

    Ok(msgs)
}

pub fn build_chan_ack_and_send(opts: &ChannelOpenOptions) -> Result<String, Error> {
    // Get the source and destination chains.
    let (src_chain, _) = ChainRuntime::spawn(opts.clone().src_chain_config)?;
    let (dst_chain, _) = ChainRuntime::spawn(opts.clone().dst_chain_config)?;

    let new_msgs = build_chan_ack(dst_chain.clone(), src_chain, opts)?;
    let key = dst_chain.get_key().map_err(|e| Kind::KeyBase.context(e))?;

    Ok(dst_chain.send_tx(new_msgs, key, "".to_string(), 0)?)
}

pub fn build_chan_confirm(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    opts: &ChannelOpenOptions,
) -> Result<Vec<Any>, Error> {
    // Check that the destination chain will accept the message
    let _dest_expected_channel = validated_expected_channel(
        dst_chain.clone(),
        src_chain.clone(),
        ChannelMsgType::OpenConfirm,
        opts,
    )
    .map_err(|e| {
        Kind::ChanOpenConfirm(
            opts.src_channel_id.clone(),
            "confirm options inconsistent with existing channel on destination chain".to_string(),
        )
        .context(e)
    })?;

    let _src_channel = src_chain
        .query_channel(
            &opts.src_port_id,
            &opts.src_channel_id,
            ICSHeight::default(),
        )
        .map_err(|e| {
            Kind::ChanOpenConfirm(
                opts.dst_channel_id.clone(),
                "channel does not exist on source".into(),
            )
            .context(e)
        })?;

    // Retrieve the connection
    let dest_connection =
        dst_chain.query_connection(&opts.dst_connection_id.clone(), ICSHeight::default())?;

    let ics_target_height = src_chain.query_latest_height()?;

    // Build message to update client on destination
    let mut msgs = build_update_client(
        dst_chain.clone(),
        src_chain.clone(),
        dest_connection.client_id().clone(),
        ics_target_height,
    )?;

    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    // Build the domain type message
    let new_msg = MsgChannelOpenConfirm {
        port_id: opts.dst_port_id.clone(),
        channel_id: opts.dst_channel_id.clone(),
        proofs: src_chain.build_channel_proofs(
            &opts.src_port_id,
            &opts.src_channel_id,
            ics_target_height,
        )?,
        signer,
    };

    let mut new_msgs = vec![new_msg.to_any::<RawMsgChannelOpenConfirm>()];

    msgs.append(&mut new_msgs);

    Ok(msgs)
}

pub fn build_chan_confirm_and_send(opts: &ChannelOpenOptions) -> Result<String, Error> {
    // Get the source and destination chains.
    let (src_chain, _) = ChainRuntime::spawn(opts.clone().src_chain_config)?;
    let (dst_chain, _) = ChainRuntime::spawn(opts.clone().dst_chain_config)?;

    let new_msgs = build_chan_confirm(dst_chain.clone(), src_chain, opts)?;
    let key = dst_chain.get_key().map_err(|e| Kind::KeyBase.context(e))?;

    Ok(dst_chain.send_tx(new_msgs, key, "".to_string(), 0)?)
}
