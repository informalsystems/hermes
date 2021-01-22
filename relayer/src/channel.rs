use std::time::SystemTime;

use prost_types::Any;
use thiserror::Error;
use tracing::{debug, error, info};

use ibc_proto::ibc::core::channel::v1::MsgChannelOpenAck as RawMsgChannelOpenAck;
use ibc_proto::ibc::core::channel::v1::MsgChannelOpenConfirm as RawMsgChannelOpenConfirm;
use ibc_proto::ibc::core::channel::v1::MsgChannelOpenInit as RawMsgChannelOpenInit;
use ibc_proto::ibc::core::channel::v1::MsgChannelOpenTry as RawMsgChannelOpenTry;

use ibc::events::IBCEvent;
use ibc::ics04_channel::channel::{ChannelEnd, Counterparty, Order, State};
use ibc::ics04_channel::msgs::chan_open_ack::MsgChannelOpenAck;
use ibc::ics04_channel::msgs::chan_open_confirm::MsgChannelOpenConfirm;
use ibc::ics04_channel::msgs::chan_open_init::MsgChannelOpenInit;
use ibc::ics04_channel::msgs::chan_open_try::MsgChannelOpenTry;
use ibc::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use ibc::tx_msg::Msg;
use ibc::Height;

use crate::chain::handle::ChainHandle;
use crate::connection::Connection;
use crate::error::{Error, Kind};
use crate::foreign_client::build_update_client;
use crate::relay::MAX_ITER;

#[derive(Debug, Error)]
pub enum ChannelError {
    #[error("failed")]
    Failed(String),
}

#[derive(Clone, Debug)]
pub struct ChannelConfigSide {
    chain_id: ChainId,
    client_id: ClientId,
    connection_id: ConnectionId,
    port_id: PortId,
    channel_id: ChannelId,
}

impl ChannelConfigSide {
    pub fn new(
        chain_id: ChainId,
        client_id: ClientId,
        connection_id: ConnectionId,
        port_id: PortId,
        channel_id: ChannelId,
    ) -> ChannelConfigSide {
        Self {
            chain_id,
            client_id,
            connection_id,
            port_id,
            channel_id,
        }
    }

    pub fn chain_id(&self) -> &ChainId {
        &self.chain_id
    }

    pub fn client_id(&self) -> &ClientId {
        &self.client_id
    }

    pub fn connection_id(&self) -> &ConnectionId {
        &self.connection_id
    }

    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }

    pub fn channel_id(&self) -> &ChannelId {
        &self.channel_id
    }
}

#[derive(Clone, Debug)]
pub struct ChannelConfig {
    pub ordering: Order,
    pub a_config: ChannelConfigSide,
    pub b_config: ChannelConfigSide,
}

impl ChannelConfig {
    pub fn src(&self) -> &ChannelConfigSide {
        &self.a_config
    }

    pub fn dst(&self) -> &ChannelConfigSide {
        &self.b_config
    }

    pub fn a_end(&self) -> &ChannelConfigSide {
        &self.a_config
    }

    pub fn b_end(&self) -> &ChannelConfigSide {
        &self.b_config
    }

    pub fn flipped(&self) -> ChannelConfig {
        ChannelConfig {
            ordering: self.ordering,
            a_config: self.b_config.clone(),
            b_config: self.a_config.clone(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Channel {
    pub config: ChannelConfig,
    connection: Connection,
}

impl Channel {
    /// Creates a new channel on top of the existing connection. If the channel is not already
    /// set-up on both sides of the connection, this functions also fulfils the channel handshake.
    pub fn new(
        connection: Connection,
        ordering: Order,
        a_port: PortId,
        b_port: PortId,
    ) -> Result<Channel, ChannelError> {
        let config = ChannelConfig {
            ordering,
            a_config: ChannelConfigSide::new(
                connection.config.a_config.chain_id().clone(),
                connection.config.a_config.client_id().clone(),
                connection.config.a_config.connection_id().clone(),
                a_port,
                Default::default(),
            ),
            b_config: ChannelConfigSide::new(
                connection.config.b_config.chain_id().clone(),
                connection.config.b_config.client_id().clone(),
                connection.config.b_config.connection_id().clone(),
                b_port,
                Default::default(),
            ),
        };
        let mut channel = Channel { config, connection };
        channel.handshake()?;
        Ok(channel)
    }

    /// Returns the underlying connection of this channel
    pub fn connection(&self) -> Connection {
        self.connection.clone()
    }

    /// Executes the channel handshake protocol (ICS004)
    fn handshake(&mut self) -> Result<(), ChannelError> {
        let done = '\u{1F973}';

        let a_chain = self.connection.chain_a();
        let b_chain = self.connection.chain_b();

        let mut flipped = self.config.flipped();

        // Try chanOpenInit on a_chain
        let now = SystemTime::now();
        let mut counter = 0;
        while counter < MAX_ITER {
            counter += 1;
            match build_chan_init_and_send(a_chain.clone(), b_chain.clone(), &flipped) {
                Err(e) => {
                    error!("Failed ChanInit {:?}: {}", self.config.a_end(), e);
                    continue;
                }
                Ok(result) => {
                    self.config.a_config.channel_id = extract_channel_id(&result)?.clone();
                    info!("{}  {} => {:?}\n", done, a_chain.id(), result);
                    break;
                }
            }
        }
        debug!("elapsed time {:?}", now.elapsed().unwrap().as_secs());
        let now = SystemTime::now();

        // Try chanOpenTry on b_chain
        counter = 0;
        while counter < MAX_ITER {
            counter += 1;
            match build_chan_try_and_send(b_chain.clone(), a_chain.clone(), &self.config) {
                Err(e) => {
                    error!("Failed ChanTry {:?}: {}", self.config.b_end(), e);
                    continue;
                }
                Ok(result) => match result {
                    IBCEvent::ChainError(e) => {
                        info!("Failed ChanTry {:?}: {}", self.config.b_end(), e);
                        continue;
                    }

                    _ => {
                        self.config.b_config.channel_id = extract_channel_id(&result)?.clone();
                        info!("{}  {} => {:?}\n", done, b_chain.id(), result);
                        break;
                    }
                },
            }
        }
        debug!("elapsed time {:?}", now.elapsed().unwrap().as_secs());

        flipped = self.config.flipped();
        counter = 0;
        while counter < MAX_ITER {
            counter += 1;
            let now = SystemTime::now();

            // Continue loop if query error
            let a_channel = a_chain.query_channel(
                &self.config.a_end().port_id,
                &self.config.a_end().channel_id,
                Height::zero(),
            );
            if a_channel.is_err() {
                continue;
            }
            let b_channel = b_chain.query_channel(
                &self.config.b_end().port_id,
                &self.config.b_end().channel_id,
                Height::zero(),
            );
            if b_channel.is_err() {
                continue;
            }

            match (
                a_channel.unwrap().state().clone(),
                b_channel.unwrap().state().clone(),
            ) {
                (State::Init, State::TryOpen) | (State::TryOpen, State::TryOpen) => {
                    // Ack to src
                    match build_chan_ack_and_send(a_chain.clone(), b_chain.clone(), &flipped) {
                        Err(e) => error!("Failed ChanAck {:?}: {}", self.config.a_end(), e),
                        Ok(event) => info!("{}  {} => {:?}\n", done, a_chain.id(), event),
                    }
                }
                (State::Open, State::TryOpen) => {
                    // Confirm to dest
                    match build_chan_confirm_and_send(
                        b_chain.clone(),
                        a_chain.clone(),
                        &self.config,
                    ) {
                        Err(e) => error!("Failed ChanConfirm {:?}: {}", self.config.b_end(), e),
                        Ok(event) => info!("{}  {} => {:?}\n", done, b_chain.id(), event),
                    }
                }
                (State::TryOpen, State::Open) => {
                    // Confirm to src
                    match build_chan_confirm_and_send(a_chain.clone(), b_chain.clone(), &flipped) {
                        Err(e) => error!("Failed ChanConfirm {:?}: {}", self.config.a_end(), e),
                        Ok(event) => info!("{}  {} => {:?}\n", done, a_chain.id(), event),
                    }
                }
                (State::Open, State::Open) => {
                    info!(
                        "{}  {}  {}  Channel handshake finished for {:#?}\n",
                        done, done, done, self.config
                    );
                    return Ok(());
                }
                _ => {} // TODO channel close
            }
            debug!("elapsed time {:?}\n", now.elapsed().unwrap().as_secs());
        }

        Err(ChannelError::Failed(format!(
            "Failed to finish channel handshake in {:?} iterations",
            MAX_ITER
        )))
    }
}

fn extract_channel_id(event: &IBCEvent) -> Result<&ChannelId, ChannelError> {
    match event {
        IBCEvent::OpenInitChannel(ev) => ev.channel_id().as_ref(),
        IBCEvent::OpenTryChannel(ev) => ev.channel_id().as_ref(),
        IBCEvent::OpenAckChannel(ev) => ev.channel_id().as_ref(),
        IBCEvent::OpenConfirmChannel(ev) => ev.channel_id().as_ref(),
        _ => None,
    }
    .ok_or_else(|| ChannelError::Failed("cannot extract channel_id from result".to_string()))
}

/// Enumeration of proof carrying ICS4 message, helper for relayer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChannelMsgType {
    OpenTry,
    OpenAck,
    OpenConfirm,
}

pub fn build_chan_init(
    dst_chain: Box<dyn ChainHandle>,
    _src_chain: Box<dyn ChainHandle>,
    opts: &ChannelConfig,
) -> Result<Vec<Any>, Error> {
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    let counterparty = Counterparty::new(opts.src().port_id().clone(), None);

    let channel = ChannelEnd::new(
        State::Init,
        opts.ordering,
        counterparty,
        vec![opts.dst().connection_id().clone()],
        dst_chain.module_version(&opts.dst().port_id())?,
    );

    // Build the domain type message
    let new_msg = MsgChannelOpenInit {
        port_id: opts.dst().port_id().clone(),
        channel,
        signer,
    };

    Ok(vec![new_msg.to_any::<RawMsgChannelOpenInit>()])
}

pub fn build_chan_init_and_send(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &ChannelConfig,
) -> Result<IBCEvent, Error> {
    let dst_msgs = build_chan_init(dst_chain.clone(), src_chain, &opts)?;

    let events = dst_chain.send_msgs(dst_msgs)?;

    // Find the relevant event for channel init
    let result = events
        .into_iter()
        .find(|event| {
            matches!(event, IBCEvent::OpenInitChannel(_))
                || matches!(event, IBCEvent::ChainError(_))
        })
        .ok_or_else(|| Kind::ChanOpenInit("no chan init event was in the response".to_string()))?;

    match result {
        IBCEvent::OpenInitChannel(_) => Ok(result),
        IBCEvent::ChainError(e) => Err(Kind::ChanOpenInit(e).into()),
        _ => panic!("internal error"),
    }
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
        Err(Kind::ChanOpen(
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
    dst_chain: Box<dyn ChainHandle>,
    _src_chain: Box<dyn ChainHandle>,
    msg_type: ChannelMsgType,
    opts: &ChannelConfig,
) -> Result<ChannelEnd, Error> {
    // If there is a channel present on the destination chain, it should look like this:
    let counterparty = Counterparty::new(
        opts.src().port_id().clone(),
        Option::from(opts.src().channel_id().clone()),
    );

    // The highest expected state, depends on the message type:
    let highest_state = match msg_type {
        ChannelMsgType::OpenAck => State::TryOpen,
        ChannelMsgType::OpenConfirm => State::TryOpen,
        _ => State::Uninitialized,
    };

    let dst_expected_channel = ChannelEnd::new(
        highest_state,
        opts.ordering,
        counterparty,
        vec![opts.dst().connection_id().clone()],
        dst_chain.module_version(&opts.dst().port_id())?,
    );

    // Retrieve existing channel if any
    let dst_channel = dst_chain.query_channel(
        &opts.dst().port_id(),
        &opts.dst().channel_id(),
        Height::default(),
    )?;

    // Check if a connection is expected to exist on destination chain
    // A channel must exist on destination chain for Ack and Confirm Tx-es to succeed
    if dst_channel.state_matches(&State::Uninitialized) {
        return Err(Kind::ChanOpen(
            opts.src().channel_id().clone(),
            "missing channel on source chain".to_string(),
        )
        .into());
    }

    check_destination_channel_state(
        opts.dst().channel_id().clone(),
        dst_channel,
        dst_expected_channel.clone(),
    )?;

    Ok(dst_expected_channel)
}

pub fn build_chan_try(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &ChannelConfig,
) -> Result<Vec<Any>, Error> {
    let src_channel = src_chain
        .query_channel(
            &opts.src().port_id(),
            &opts.src().channel_id(),
            Height::default(),
        )
        .map_err(|e| Kind::ChanOpenTry("channel does not exist on source".into()).context(e))?;

    // Retrieve the connection
    let dst_connection =
        dst_chain.query_connection(&opts.dst().connection_id().clone(), Height::default())?;

    let query_height = src_chain.query_latest_height()?;
    let proofs = src_chain.build_channel_proofs(
        &opts.src().port_id(),
        &opts.src().channel_id(),
        query_height,
    )?;

    // Build message(s) to update client on destination
    let mut msgs = build_update_client(
        dst_chain.clone(),
        src_chain.clone(),
        &dst_connection.client_id(),
        proofs.height(),
    )?;

    let counterparty = Counterparty::new(
        opts.src().port_id().clone(),
        Some(opts.src().channel_id().clone()),
    );

    let channel = ChannelEnd::new(
        State::TryOpen,
        opts.ordering,
        counterparty,
        vec![opts.dst().connection_id().clone()],
        dst_chain.module_version(&opts.dst().port_id())?,
    );

    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    // Build the domain type message
    let new_msg = MsgChannelOpenTry {
        port_id: opts.dst().port_id().clone(),
        previous_channel_id: src_channel.counterparty().channel_id.clone(),
        counterparty_version: src_chain.module_version(&opts.src().port_id())?,
        channel,
        proofs,
        signer,
    };

    let mut new_msgs = vec![new_msg.to_any::<RawMsgChannelOpenTry>()];

    msgs.append(&mut new_msgs);

    Ok(msgs)
}

pub fn build_chan_try_and_send(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &ChannelConfig,
) -> Result<IBCEvent, Error> {
    let dst_msgs = build_chan_try(dst_chain.clone(), src_chain, &opts)?;

    let events = dst_chain.send_msgs(dst_msgs)?;

    // Find the relevant event for channel try
    events
        .into_iter()
        .find(|event| {
            matches!(event, IBCEvent::OpenTryChannel(_)) || matches!(event, IBCEvent::ChainError(_))
        })
        .ok_or_else(|| {
            Kind::ChanOpenTry("no chan try event was in the response".to_string()).into()
        })
}

pub fn build_chan_ack(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &ChannelConfig,
) -> Result<Vec<Any>, Error> {
    // Check that the destination chain will accept the message
    let _dst_expected_channel = validated_expected_channel(
        dst_chain.clone(),
        src_chain.clone(),
        ChannelMsgType::OpenAck,
        opts,
    )
    .map_err(|e| {
        Kind::ChanOpenAck(
            opts.src().channel_id().clone(),
            "ack options inconsistent with existing channel on destination chain".to_string(),
        )
        .context(e)
    })?;

    let _src_channel = src_chain
        .query_channel(
            &opts.src().port_id(),
            &opts.src().channel_id(),
            Height::default(),
        )
        .map_err(|e| {
            Kind::ChanOpenAck(
                opts.dst().channel_id().clone(),
                "channel does not exist on source".into(),
            )
            .context(e)
        })?;

    // Retrieve the connection
    let dst_connection =
        dst_chain.query_connection(&opts.dst().connection_id().clone(), Height::default())?;

    let query_height = src_chain.query_latest_height()?;
    let proofs = src_chain.build_channel_proofs(
        &opts.src().port_id(),
        &opts.src().channel_id(),
        query_height,
    )?;

    // Build message(s) to update client on destination
    let mut msgs = build_update_client(
        dst_chain.clone(),
        src_chain.clone(),
        &dst_connection.client_id(),
        proofs.height(),
    )?;

    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    // Build the domain type message
    let new_msg = MsgChannelOpenAck {
        port_id: opts.dst().port_id().clone(),
        channel_id: opts.dst().channel_id().clone(),
        counterparty_channel_id: opts.src().channel_id().clone(),
        counterparty_version: src_chain.module_version(&opts.dst().port_id())?,
        proofs,
        signer,
    };

    let mut new_msgs = vec![new_msg.to_any::<RawMsgChannelOpenAck>()];

    msgs.append(&mut new_msgs);

    Ok(msgs)
}

pub fn build_chan_ack_and_send(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &ChannelConfig,
) -> Result<IBCEvent, Error> {
    let dst_msgs = build_chan_ack(dst_chain.clone(), src_chain, &opts)?;

    let events = dst_chain.send_msgs(dst_msgs)?;

    // Find the relevant event for channel ack
    events
        .into_iter()
        .find(|event| {
            matches!(event, IBCEvent::OpenAckChannel(_)) || matches!(event, IBCEvent::ChainError(_))
        })
        .ok_or_else(|| {
            Kind::ChanOpenAck(
                opts.dst().channel_id().clone(),
                "no chan ack event was in the response".to_string(),
            )
            .into()
        })
}

pub fn build_chan_confirm(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &ChannelConfig,
) -> Result<Vec<Any>, Error> {
    // Check that the destination chain will accept the message
    let _dst_expected_channel = validated_expected_channel(
        dst_chain.clone(),
        src_chain.clone(),
        ChannelMsgType::OpenConfirm,
        opts,
    )
    .map_err(|e| {
        Kind::ChanOpenConfirm(
            opts.src().channel_id().clone(),
            "confirm options inconsistent with existing channel on destination chain".to_string(),
        )
        .context(e)
    })?;

    let _src_channel = src_chain
        .query_channel(
            &opts.src().port_id(),
            &opts.src().channel_id(),
            Height::default(),
        )
        .map_err(|e| {
            Kind::ChanOpenConfirm(
                opts.src().channel_id().clone(),
                "channel does not exist on source".into(),
            )
            .context(e)
        })?;

    // Retrieve the connection
    let dst_connection =
        dst_chain.query_connection(&opts.dst().connection_id().clone(), Height::default())?;

    let query_height = src_chain.query_latest_height()?;
    let proofs = src_chain.build_channel_proofs(
        &opts.src().port_id(),
        &opts.src().channel_id(),
        query_height,
    )?;

    // Build message(s) to update client on destination
    let mut msgs = build_update_client(
        dst_chain.clone(),
        src_chain.clone(),
        &dst_connection.client_id(),
        proofs.height(),
    )?;

    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    // Build the domain type message
    let new_msg = MsgChannelOpenConfirm {
        port_id: opts.dst().port_id().clone(),
        channel_id: opts.dst().channel_id().clone(),
        proofs,
        signer,
    };

    let mut new_msgs = vec![new_msg.to_any::<RawMsgChannelOpenConfirm>()];

    msgs.append(&mut new_msgs);

    Ok(msgs)
}

pub fn build_chan_confirm_and_send(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    opts: &ChannelConfig,
) -> Result<IBCEvent, Error> {
    let dst_msgs = build_chan_confirm(dst_chain.clone(), src_chain, &opts)?;

    let events = dst_chain.send_msgs(dst_msgs)?;

    // Find the relevant event for channel confirm
    events
        .into_iter()
        .find(|event| {
            matches!(event, IBCEvent::OpenConfirmChannel(_))
                || matches!(event, IBCEvent::ChainError(_))
        })
        .ok_or_else(|| {
            Kind::ChanOpenConfirm(
                opts.dst().channel_id().clone(),
                "no chan confirm event was in the response".to_string(),
            )
            .into()
        })
}
