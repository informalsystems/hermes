use prost_types::Any;
use thiserror::Error;
use tracing::{error, info};

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
use crate::foreign_client::ForeignClient;
use crate::relay::MAX_ITER;

#[derive(Debug, Error)]
pub enum ChannelError {
    #[error("failed")]
    Failed(String),
}

#[derive(Clone, Debug)]
pub struct ChannelSide {
    pub chain: Box<dyn ChainHandle>,
    client_id: ClientId,
    connection_id: ConnectionId,
    port_id: PortId,
    channel_id: ChannelId,
}

impl ChannelSide {
    pub fn new(
        chain: Box<dyn ChainHandle>,
        client_id: ClientId,
        connection_id: ConnectionId,
        port_id: PortId,
        channel_id: ChannelId,
    ) -> ChannelSide {
        Self {
            chain,
            client_id,
            connection_id,
            port_id,
            channel_id,
        }
    }

    pub fn chain_id(&self) -> ChainId {
        self.chain.id()
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
pub struct Channel {
    pub ordering: Order,
    pub a_side: ChannelSide,
    pub b_side: ChannelSide,
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
        let mut channel = Channel {
            ordering,
            a_side: ChannelSide::new(
                connection.src_chain().clone(),
                connection.src_client_id().clone(),
                connection.src_connection_id().clone(),
                a_port,
                Default::default(),
            ),
            b_side: ChannelSide::new(
                connection.dst_chain().clone(),
                connection.dst_client_id().clone(),
                connection.dst_connection_id().clone(),
                b_port,
                Default::default(),
            ),
        };
        channel.handshake()?;
        Ok(channel)
    }

    pub fn src_chain(&self) -> Box<dyn ChainHandle> {
        self.a_side.chain.clone()
    }

    pub fn dst_chain(&self) -> Box<dyn ChainHandle> {
        self.b_side.chain.clone()
    }

    pub fn src_client_id(&self) -> &ClientId {
        &self.a_side.client_id
    }

    pub fn dst_client_id(&self) -> &ClientId {
        &self.b_side.client_id
    }

    pub fn src_connection_id(&self) -> &ConnectionId {
        &self.a_side.connection_id
    }

    pub fn dst_connection_id(&self) -> &ConnectionId {
        &self.b_side.connection_id
    }

    pub fn src_port_id(&self) -> &PortId {
        &self.a_side.port_id
    }

    pub fn dst_port_id(&self) -> &PortId {
        &self.b_side.port_id
    }

    pub fn src_channel_id(&self) -> &ChannelId {
        &self.a_side.channel_id
    }

    pub fn dst_channel_id(&self) -> &ChannelId {
        &self.b_side.channel_id
    }

    pub fn flipped(&self) -> Channel {
        Channel {
            ordering: self.ordering,
            a_side: self.b_side.clone(),
            b_side: self.a_side.clone(),
        }
    }

    /// Executes the channel handshake protocol (ICS004)
    fn handshake(&mut self) -> Result<(), ChannelError> {
        let done = '\u{1F973}';

        let a_chain = self.src_chain();
        let b_chain = self.dst_chain();

        // Try chanOpenInit on a_chain
        let mut counter = 0;
        while counter < MAX_ITER {
            counter += 1;
            match self.flipped().build_chan_init_and_send() {
                Err(e) => {
                    error!("Failed ChanInit {:?}: {}", self.a_side, e);
                    continue;
                }
                Ok(result) => {
                    self.a_side.channel_id = extract_channel_id(&result)?.clone();
                    info!("{}  {} => {:?}\n", done, a_chain.id(), result);
                    break;
                }
            }
        }

        // Try chanOpenTry on b_chain
        counter = 0;
        while counter < MAX_ITER {
            counter += 1;
            match self.build_chan_try_and_send() {
                Err(e) => {
                    error!("Failed ChanTry {:?}: {}", self.b_side, e);
                    continue;
                }
                Ok(result) => match result {
                    IBCEvent::ChainError(e) => {
                        info!("Failed ChanTry {:?}: {}", self.b_side, e);
                        continue;
                    }

                    _ => {
                        self.b_side.channel_id = extract_channel_id(&result)?.clone();
                        info!("{}  {} => {:?}\n", done, b_chain.id(), result);
                        break;
                    }
                },
            }
        }

        counter = 0;
        while counter < MAX_ITER {
            counter += 1;

            // Continue loop if query error
            let a_channel =
                a_chain.query_channel(&self.src_port_id(), &self.src_channel_id(), Height::zero());
            if a_channel.is_err() {
                continue;
            }
            let b_channel =
                b_chain.query_channel(&self.dst_port_id(), &self.dst_channel_id(), Height::zero());
            if b_channel.is_err() {
                continue;
            }

            match (
                a_channel.unwrap().state().clone(),
                b_channel.unwrap().state().clone(),
            ) {
                (State::Init, State::TryOpen) | (State::TryOpen, State::TryOpen) => {
                    // Ack to a_chain
                    match self.flipped().build_chan_ack_and_send() {
                        Err(e) => error!("Failed ChanAck {:?}: {}", self.a_side, e),
                        Ok(event) => info!("{}  {} => {:?}\n", done, a_chain.id(), event),
                    }
                }
                (State::Open, State::TryOpen) => {
                    // Confirm to b_chain
                    match self.build_chan_confirm_and_send() {
                        Err(e) => error!("Failed ChanConfirm {:?}: {}", self.b_side, e),
                        Ok(event) => info!("{}  {} => {:?}\n", done, b_chain.id(), event),
                    }
                }
                (State::TryOpen, State::Open) => {
                    // Confirm to a_chain
                    match self.flipped().build_chan_confirm_and_send() {
                        Err(e) => error!("Failed ChanConfirm {:?}: {}", self.a_side, e),
                        Ok(event) => info!("{}  {} => {:?}\n", done, a_chain.id(), event),
                    }
                }
                (State::Open, State::Open) => {
                    info!(
                        "{}  {}  {}  Channel handshake finished for {:#?}\n",
                        done, done, done, self
                    );
                    return Ok(());
                }
                _ => {} // TODO channel close
            }
        }

        Err(ChannelError::Failed(format!(
            "Failed to finish channel handshake in {:?} iterations",
            MAX_ITER
        )))
    }

    pub fn build_update_client_on_dst(&self, height: Height) -> Result<Vec<Any>, Error> {
        let client = ForeignClient {
            id: self.dst_client_id().clone(),
            dst_chain: self.dst_chain(),
            src_chain: self.src_chain(),
        };

        client.build_update_client(height)
    }

    pub fn build_chan_init(&self) -> Result<Vec<Any>, Error> {
        let signer = self
            .dst_chain()
            .get_signer()
            .map_err(|e| Kind::KeyBase.context(e))?;

        let counterparty = Counterparty::new(self.src_port_id().clone(), None);

        let channel = ChannelEnd::new(
            State::Init,
            self.ordering,
            counterparty,
            vec![self.dst_connection_id().clone()],
            self.dst_chain().module_version(self.dst_port_id())?,
        );

        // Build the domain type message
        let new_msg = MsgChannelOpenInit {
            port_id: self.dst_port_id().clone(),
            channel,
            signer,
        };

        Ok(vec![new_msg.to_any::<RawMsgChannelOpenInit>()])
    }

    pub fn build_chan_init_and_send(&self) -> Result<IBCEvent, Error> {
        let dst_msgs = self.build_chan_init()?;

        let events = self.dst_chain().send_msgs(dst_msgs)?;

        // Find the relevant event for channel init
        let result = events
            .into_iter()
            .find(|event| {
                matches!(event, IBCEvent::OpenInitChannel(_))
                    || matches!(event, IBCEvent::ChainError(_))
            })
            .ok_or_else(|| {
                Kind::ChanOpenInit("no chan init event was in the response".to_string())
            })?;

        match result {
            IBCEvent::OpenInitChannel(_) => Ok(result),
            IBCEvent::ChainError(e) => Err(Kind::ChanOpenInit(e).into()),
            _ => panic!("internal error"),
        }
    }

    /// Retrieves the channel from destination and compares against the expected channel
    /// built from the message type (`msg_type`) and options (`opts`).
    /// If the expected and the destination channels are compatible, it returns the expected channel
    fn validated_expected_channel(&self, msg_type: ChannelMsgType) -> Result<ChannelEnd, Error> {
        // If there is a channel present on the destination chain, it should look like this:
        let counterparty = Counterparty::new(
            self.src_port_id().clone(),
            Option::from(self.src_channel_id().clone()),
        );

        // The highest expected state, depends on the message type:
        let highest_state = match msg_type {
            ChannelMsgType::OpenAck => State::TryOpen,
            ChannelMsgType::OpenConfirm => State::TryOpen,
            _ => State::Uninitialized,
        };

        let dst_expected_channel = ChannelEnd::new(
            highest_state,
            self.ordering,
            counterparty,
            vec![self.dst_connection_id().clone()],
            self.dst_chain().module_version(self.dst_port_id())?,
        );

        // Retrieve existing channel if any
        let dst_channel = self.dst_chain().query_channel(
            self.dst_port_id(),
            self.dst_channel_id(),
            Height::default(),
        )?;

        // Check if a connection is expected to exist on destination chain
        // A channel must exist on destination chain for Ack and Confirm Tx-es to succeed
        if dst_channel.state_matches(&State::Uninitialized) {
            return Err(Kind::ChanOpen(
                self.src_channel_id().clone(),
                "missing channel on source chain".to_string(),
            )
            .into());
        }

        check_destination_channel_state(
            self.dst_channel_id().clone(),
            dst_channel,
            dst_expected_channel.clone(),
        )?;

        Ok(dst_expected_channel)
    }

    pub fn build_chan_try(&self) -> Result<Vec<Any>, Error> {
        let src_channel = self
            .src_chain()
            .query_channel(self.src_port_id(), self.src_channel_id(), Height::default())
            .map_err(|e| Kind::ChanOpenTry("channel does not exist on source".into()).context(e))?;

        // Retrieve the connection
        let _dst_connection = self
            .dst_chain()
            .query_connection(self.dst_connection_id(), Height::default())?;

        let query_height = self.src_chain().query_latest_height()?;
        let proofs = self.src_chain().build_channel_proofs(
            self.src_port_id(),
            self.src_channel_id(),
            query_height,
        )?;

        // Build message(s) to update client on destination
        let mut msgs = self.build_update_client_on_dst(proofs.height())?;

        let counterparty = Counterparty::new(
            self.src_port_id().clone(),
            Some(self.src_channel_id().clone()),
        );

        let channel = ChannelEnd::new(
            State::TryOpen,
            self.ordering,
            counterparty,
            vec![self.dst_connection_id().clone()],
            self.dst_chain().module_version(self.dst_port_id())?,
        );

        // Get signer
        let signer = self
            .dst_chain()
            .get_signer()
            .map_err(|e| Kind::KeyBase.context(e))?;

        // Build the domain type message
        let new_msg = MsgChannelOpenTry {
            port_id: self.dst_port_id().clone(),
            previous_channel_id: src_channel.counterparty().channel_id.clone(),
            counterparty_version: self.src_chain().module_version(self.src_port_id())?,
            channel,
            proofs,
            signer,
        };

        let mut new_msgs = vec![new_msg.to_any::<RawMsgChannelOpenTry>()];

        msgs.append(&mut new_msgs);

        Ok(msgs)
    }

    pub fn build_chan_try_and_send(&self) -> Result<IBCEvent, Error> {
        let dst_msgs = self.build_chan_try()?;

        let events = self.dst_chain().send_msgs(dst_msgs)?;

        // Find the relevant event for channel try
        events
            .into_iter()
            .find(|event| {
                matches!(event, IBCEvent::OpenTryChannel(_))
                    || matches!(event, IBCEvent::ChainError(_))
            })
            .ok_or_else(|| {
                Kind::ChanOpenTry("no chan try event was in the response".to_string()).into()
            })
    }

    pub fn build_chan_ack(&self) -> Result<Vec<Any>, Error> {
        // Check that the destination chain will accept the message
        let _dst_expected_channel = self
            .validated_expected_channel(ChannelMsgType::OpenAck)
            .map_err(|e| {
                Kind::ChanOpenAck(
                    self.src_channel_id().clone(),
                    "ack options inconsistent with existing channel on destination chain"
                        .to_string(),
                )
                .context(e)
            })?;

        let _src_channel = self
            .src_chain()
            .query_channel(self.src_port_id(), self.src_channel_id(), Height::default())
            .map_err(|e| {
                Kind::ChanOpenAck(
                    self.src_channel_id().clone(),
                    "channel does not exist on source".into(),
                )
                .context(e)
            })?;

        // Retrieve the connection
        let _dst_connection = self
            .dst_chain()
            .query_connection(self.dst_connection_id(), Height::default())?;

        let query_height = self.src_chain().query_latest_height()?;
        let proofs = self.src_chain().build_channel_proofs(
            self.src_port_id(),
            self.src_channel_id(),
            query_height,
        )?;

        // Build message(s) to update client on destination
        let mut msgs = self.build_update_client_on_dst(proofs.height())?;

        // Get signer
        let signer = self
            .dst_chain()
            .get_signer()
            .map_err(|e| Kind::KeyBase.context(e))?;

        // Build the domain type message
        let new_msg = MsgChannelOpenAck {
            port_id: self.dst_port_id().clone(),
            channel_id: self.dst_channel_id().clone(),
            counterparty_channel_id: self.src_channel_id().clone(),
            counterparty_version: self.src_chain().module_version(self.src_port_id())?,
            proofs,
            signer,
        };

        let mut new_msgs = vec![new_msg.to_any::<RawMsgChannelOpenAck>()];

        msgs.append(&mut new_msgs);

        Ok(msgs)
    }

    pub fn build_chan_ack_and_send(&self) -> Result<IBCEvent, Error> {
        let dst_msgs = self.build_chan_ack()?;

        let events = self.dst_chain().send_msgs(dst_msgs)?;

        // Find the relevant event for channel ack
        events
            .into_iter()
            .find(|event| {
                matches!(event, IBCEvent::OpenAckChannel(_))
                    || matches!(event, IBCEvent::ChainError(_))
            })
            .ok_or_else(|| {
                Kind::ChanOpenAck(
                    self.dst_channel_id().clone(),
                    "no chan ack event was in the response".to_string(),
                )
                .into()
            })
    }

    pub fn build_chan_confirm(&self) -> Result<Vec<Any>, Error> {
        // Check that the destination chain will accept the message
        let _dst_expected_channel = self
            .validated_expected_channel(ChannelMsgType::OpenConfirm)
            .map_err(|e| {
                Kind::ChanOpenConfirm(
                    self.src_channel_id().clone(),
                    "confirm options inconsistent with existing channel on destination chain"
                        .to_string(),
                )
                .context(e)
            })?;

        let _src_channel = self
            .src_chain()
            .query_channel(self.src_port_id(), self.src_channel_id(), Height::default())
            .map_err(|e| {
                Kind::ChanOpenConfirm(
                    self.src_channel_id().clone(),
                    "channel does not exist on source".into(),
                )
                .context(e)
            })?;

        // Retrieve the connection
        let _dst_connection = self
            .dst_chain()
            .query_connection(self.dst_connection_id(), Height::default())?;

        let query_height = self.src_chain().query_latest_height()?;
        let proofs = self.src_chain().build_channel_proofs(
            self.src_port_id(),
            self.src_channel_id(),
            query_height,
        )?;

        // Build message(s) to update client on destination
        let mut msgs = self.build_update_client_on_dst(proofs.height())?;

        // Get signer
        let signer = self
            .dst_chain()
            .get_signer()
            .map_err(|e| Kind::KeyBase.context(e))?;

        // Build the domain type message
        let new_msg = MsgChannelOpenConfirm {
            port_id: self.dst_port_id().clone(),
            channel_id: self.dst_channel_id().clone(),
            proofs,
            signer,
        };

        let mut new_msgs = vec![new_msg.to_any::<RawMsgChannelOpenConfirm>()];

        msgs.append(&mut new_msgs);

        Ok(msgs)
    }

    pub fn build_chan_confirm_and_send(&self) -> Result<IBCEvent, Error> {
        let dst_msgs = self.build_chan_confirm()?;

        let events = self.dst_chain().send_msgs(dst_msgs)?;

        // Find the relevant event for channel confirm
        events
            .into_iter()
            .find(|event| {
                matches!(event, IBCEvent::OpenConfirmChannel(_))
                    || matches!(event, IBCEvent::ChainError(_))
            })
            .ok_or_else(|| {
                Kind::ChanOpenConfirm(
                    self.dst_channel_id().clone(),
                    "no chan confirm event was in the response".to_string(),
                )
                .into()
            })
    }
}

fn extract_channel_id(event: &IBCEvent) -> Result<&ChannelId, ChannelError> {
    match event {
        IBCEvent::OpenInitChannel(ev) => Ok(ev.channel_id()),
        IBCEvent::OpenTryChannel(ev) => Ok(ev.channel_id()),
        IBCEvent::OpenAckChannel(ev) => Ok(ev.channel_id()),
        IBCEvent::OpenConfirmChannel(ev) => Ok(ev.channel_id()),
        _ => Err(ChannelError::Failed(
            "cannot extract channel_id from result".to_string(),
        )),
    }
}

/// Enumeration of proof carrying ICS4 message, helper for relayer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChannelMsgType {
    OpenTry,
    OpenAck,
    OpenConfirm,
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
