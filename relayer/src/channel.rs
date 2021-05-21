use prost_types::Any;
use serde::Serialize;
use thiserror::Error;
use tracing::error;

use ibc::events::IbcEvent;
use ibc::ics04_channel::channel::{ChannelEnd, Counterparty, Order, State};
use ibc::ics04_channel::msgs::chan_close_confirm::MsgChannelCloseConfirm;
use ibc::ics04_channel::msgs::chan_close_init::MsgChannelCloseInit;
use ibc::ics04_channel::msgs::chan_open_ack::MsgChannelOpenAck;
use ibc::ics04_channel::msgs::chan_open_confirm::MsgChannelOpenConfirm;
use ibc::ics04_channel::msgs::chan_open_init::MsgChannelOpenInit;
use ibc::ics04_channel::msgs::chan_open_try::MsgChannelOpenTry;
use ibc::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use ibc::tx_msg::Msg;
use ibc::Height;

use crate::chain::handle::ChainHandle;
use crate::connection::Connection;
use crate::error::Error;
use crate::foreign_client::{ForeignClient, ForeignClientError};
use crate::relay::MAX_ITER;
use std::time::Duration;

#[derive(Debug, Error)]
pub enum ChannelError {
    #[error("failed with underlying cause: {0}")]
    Failed(String),

    #[error("failed during an operation on client ({0}) hosted by chain ({1}) with error: {2}")]
    ClientOperation(ClientId, ChainId, ForeignClientError),

    #[error("failed during a query to chain id {0} with underlying error: {1}")]
    QueryError(ChainId, Error),

    #[error(
        "failed during a transaction submission step to chain id {0} with underlying error: {1}"
    )]
    SubmitError(ChainId, Error),
}

#[derive(Clone, Debug, Serialize)]
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

#[derive(Clone, Debug, Serialize)]
pub struct Channel {
    pub ordering: Order,
    pub a_side: ChannelSide,
    pub b_side: ChannelSide,
    pub connection_delay: Duration,
    pub version: Option<String>,
}

impl Channel {
    /// Creates a new channel on top of the existing connection. If the channel is not already
    /// set-up on both sides of the connection, this functions also fulfils the channel handshake.
    pub fn new(
        connection: Connection,
        ordering: Order,
        a_port: PortId,
        b_port: PortId,
        version: Option<String>,
    ) -> Result<Self, ChannelError> {
        let b_side_chain = connection.dst_chain().clone();
        let version = version.unwrap_or(
            b_side_chain
                .module_version(&a_port)
                .map_err(|e| ChannelError::QueryError(b_side_chain.id(), e))?,
        );

        let mut channel = Self {
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
            connection_delay: connection.delay_period,
            version: Some(version),
        };

        channel.handshake()?;

        Ok(channel)
    }

    pub fn src_chain(&self) -> &Box<dyn ChainHandle> {
        &self.a_side.chain
    }

    pub fn dst_chain(&self) -> &Box<dyn ChainHandle> {
        &self.b_side.chain
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
            connection_delay: self.connection_delay,
            version: self.version.clone(),
        }
    }

    /// Executes the channel handshake protocol (ICS004)
    fn handshake(&mut self) -> Result<(), ChannelError> {
        let done = '🥳';

        let a_chain = self.src_chain().clone();
        let b_chain = self.dst_chain().clone();

        // Try chanOpenInit on a_chain
        let mut counter = 0;
        let mut init_success = false;
        while counter < MAX_ITER {
            counter += 1;
            match self.flipped().build_chan_open_init_and_send() {
                Err(e) => {
                    error!("Failed ChanInit {:?}: {:?}", self.a_side, e);
                    continue;
                }
                Ok(event) => {
                    self.a_side.channel_id = extract_channel_id(&event)?.clone();
                    println!("{}  {} => {:#?}\n", done, a_chain.id(), event);
                    init_success = true;
                    break;
                }
            }
        }

        // Check that the channel was created on a_chain
        if !init_success {
            return Err(ChannelError::Failed(format!(
                "Failed to finish channel open init in {} iterations for {:?}",
                MAX_ITER, self
            )));
        };

        // Try chanOpenTry on b_chain
        counter = 0;
        let mut try_success = false;
        while counter < MAX_ITER {
            counter += 1;
            match self.build_chan_open_try_and_send() {
                Err(e) => {
                    error!("Failed ChanTry {:?}: {:?}", self.b_side, e);
                    continue;
                }
                Ok(event) => {
                    self.b_side.channel_id = extract_channel_id(&event)?.clone();
                    println!("{}  {} => {:#?}\n", done, b_chain.id(), event);
                    try_success = true;
                    break;
                }
            }
        }

        if !try_success {
            return Err(ChannelError::Failed(format!(
                "Failed to finish channel open try in {} iterations for {:?}",
                MAX_ITER, self
            )));
        };

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

            match (a_channel.unwrap().state(), b_channel.unwrap().state()) {
                (State::Init, State::TryOpen) | (State::TryOpen, State::TryOpen) => {
                    // Ack to a_chain
                    match self.flipped().build_chan_open_ack_and_send() {
                        Err(e) => error!("Failed ChanAck {:?}: {}", self.a_side, e),
                        Ok(event) => println!("{}  {} => {:#?}\n", done, a_chain.id(), event),
                    }
                }
                (State::Open, State::TryOpen) => {
                    // Confirm to b_chain
                    match self.build_chan_open_confirm_and_send() {
                        Err(e) => error!("Failed ChanConfirm {:?}: {}", self.b_side, e),
                        Ok(event) => println!("{}  {} => {:#?}\n", done, b_chain.id(), event),
                    }
                }
                (State::TryOpen, State::Open) => {
                    // Confirm to a_chain
                    match self.flipped().build_chan_open_confirm_and_send() {
                        Err(e) => error!("Failed ChanConfirm {:?}: {}", self.a_side, e),
                        Ok(event) => println!("{}  {} => {:#?}\n", done, a_chain.id(), event),
                    }
                }
                (State::Open, State::Open) => {
                    println!(
                        "{}  {}  {}  Channel handshake finished for {:#?}\n",
                        done, done, done, self
                    );
                    return Ok(());
                }
                _ => {} // TODO channel close
            }
        }

        Err(ChannelError::Failed(format!(
            "Failed to finish channel handshake in {} iterations for {:?}",
            MAX_RETRIES, self
        )))
    }

    pub fn build_update_client_on_dst(&self, height: Height) -> Result<Vec<Any>, ChannelError> {
        let client = ForeignClient::restore(
            self.dst_client_id().clone(),
            self.dst_chain().clone(),
            self.src_chain().clone(),
        );

        client.build_update_client(height).map_err(|e| {
            ChannelError::ClientOperation(self.dst_client_id().clone(), self.dst_chain().id(), e)
        })
    }

    /// Returns the channel version if already set, otherwise it queries the destination chain
    /// for the destination port's version.
    /// Note: This query is currently not available and it is hardcoded in the `module_version()`
    /// to be `ics20-1` for `transfer` port.
    pub fn dst_version(&self) -> Result<String, ChannelError> {
        Ok(self.version.clone()
            .unwrap_or(
                self
                    .dst_chain()
                    .module_version(self.dst_port_id())
                    .map_err(|e| {
                        ChannelError::Failed(format!(
                            "failed while getting the module version from dst chain ({}) with error: {}",
                            self.dst_chain().id(),
                            e
                        ))
                    })?
            ))
    }

    /// Returns the channel version if already set, otherwise it queries the source chain
    /// for the source port's version.
    pub fn src_version(&self) -> Result<String, ChannelError> {
        Ok(self.version.clone()
            .unwrap_or(
                self
                    .src_chain()
                    .module_version(self.src_port_id())
                    .map_err(|e| {
                        ChannelError::Failed(format!(
                            "failed while getting the module version from src chain ({}) with error: {}",
                            self.src_chain().id(),
                            e
                        ))
                    })?
            ))
    }

    pub fn build_chan_open_init(&self) -> Result<Vec<Any>, ChannelError> {
        let signer = self.dst_chain().get_signer().map_err(|e| {
            ChannelError::Failed(format!(
                "failed while fetching the signer for dst chain ({}) with error: {}",
                self.dst_chain().id(),
                e
            ))
        })?;

        let counterparty = Counterparty::new(self.src_port_id().clone(), None);

        let channel = ChannelEnd::new(
            State::Init,
            self.ordering,
            counterparty,
            vec![self.dst_connection_id().clone()],
            self.dst_version()?,
        );

        // Build the domain type message
        let new_msg = MsgChannelOpenInit {
            port_id: self.dst_port_id().clone(),
            channel,
            signer,
        };

        Ok(vec![new_msg.to_any()])
    }

    pub fn build_chan_open_init_and_send(&self) -> Result<IbcEvent, ChannelError> {
        let dst_msgs = self.build_chan_open_init()?;

        let events = self
            .dst_chain()
            .send_msgs(dst_msgs)
            .map_err(|e| ChannelError::SubmitError(self.dst_chain().id(), e))?;

        // Find the relevant event for channel open init
        let result = events
            .into_iter()
            .find(|event| {
                matches!(event, IbcEvent::OpenInitChannel(_))
                    || matches!(event, IbcEvent::ChainError(_))
            })
            .ok_or_else(|| {
                ChannelError::Failed("no chan init event was in the response".to_string())
            })?;

        match result {
            IbcEvent::OpenInitChannel(_) => Ok(result),
            IbcEvent::ChainError(e) => {
                Err(ChannelError::Failed(format!("tx response error: {}", e)))
            }
            _ => panic!("internal error"),
        }
    }

    /// Retrieves the channel from destination and compares against the expected channel
    /// built from the message type (`msg_type`) and options (`opts`).
    /// If the expected and the destination channels are compatible, it returns the expected channel
    fn validated_expected_channel(
        &self,
        msg_type: ChannelMsgType,
    ) -> Result<ChannelEnd, ChannelError> {
        // If there is a channel present on the destination chain, it should look like this:
        let counterparty = Counterparty::new(
            self.src_port_id().clone(),
            Option::from(self.src_channel_id().clone()),
        );

        // The highest expected state, depends on the message type:
        let highest_state = match msg_type {
            ChannelMsgType::OpenAck => State::TryOpen,
            ChannelMsgType::OpenConfirm => State::TryOpen,
            ChannelMsgType::CloseConfirm => State::Open,
            _ => State::Uninitialized,
        };

        let dst_expected_channel = ChannelEnd::new(
            highest_state,
            self.ordering,
            counterparty,
            vec![self.dst_connection_id().clone()],
            self.dst_version()?,
        );

        // Retrieve existing channel if any
        let dst_channel = self
            .dst_chain()
            .query_channel(self.dst_port_id(), self.dst_channel_id(), Height::default())
            .map_err(|e| ChannelError::QueryError(self.dst_chain().id(), e))?;

        // Check if a connection is expected to exist on destination chain
        // A channel must exist on destination chain for Ack and Confirm Tx-es to succeed
        if dst_channel.state_matches(&State::Uninitialized) {
            return Err(ChannelError::Failed(
                "missing channel on source chain".to_string(),
            ));
        }

        check_destination_channel_state(
            self.dst_channel_id().clone(),
            dst_channel,
            dst_expected_channel.clone(),
        )?;

        Ok(dst_expected_channel)
    }

    pub fn build_chan_open_try(&self) -> Result<Vec<Any>, ChannelError> {
        let src_channel = self
            .src_chain()
            .query_channel(self.src_port_id(), self.src_channel_id(), Height::default())
            .map_err(|e| ChannelError::QueryError(self.src_chain().id(), e))?;

        if src_channel.counterparty().port_id() != self.dst_port_id() {
            return Err(ChannelError::Failed(format!(
                "channel open try to chain `{}` and destination port `{}` does not match \
                the source chain `{}` counterparty port `{}`",
                self.dst_chain().id(),
                self.dst_port_id(),
                self.src_chain().id(),
                src_channel.counterparty().port_id,
            )));
        }

        // Retrieve the connection
        let _dst_connection = self
            .dst_chain()
            .query_connection(self.dst_connection_id(), Height::default())
            .map_err(|e| ChannelError::QueryError(self.dst_chain().id(), e))?;

        let query_height = self
            .src_chain()
            .query_latest_height()
            .map_err(|e| ChannelError::QueryError(self.src_chain().id(), e))?;

        let proofs = self
            .src_chain()
            .build_channel_proofs(self.src_port_id(), self.src_channel_id(), query_height)
            .map_err(|e| ChannelError::Failed(format!("failed to build channel proofs: {}", e)))?;

        // Build message(s) to update client on destination
        let mut msgs = self.build_update_client_on_dst(proofs.height())?;

        let counterparty = Counterparty::new(
            self.src_port_id().clone(),
            Some(self.src_channel_id().clone()),
        );

        let channel = ChannelEnd::new(
            State::TryOpen,
            *src_channel.ordering(),
            counterparty,
            vec![self.dst_connection_id().clone()],
            self.dst_version()?,
        );

        // Get signer
        let signer = self.dst_chain().get_signer().map_err(|e| {
            ChannelError::Failed(format!(
                "failed while fetching the signer for dst chain ({}) with error: {}",
                self.dst_chain().id(),
                e
            ))
        })?;

        // Build the domain type message
        let new_msg = MsgChannelOpenTry {
            port_id: self.dst_port_id().clone(),
            previous_channel_id: src_channel.counterparty().channel_id.clone(),
            counterparty_version: self.src_version()?,
            channel,
            proofs,
            signer,
        };

        msgs.push(new_msg.to_any());
        Ok(msgs)
    }

    pub fn build_chan_open_try_and_send(&self) -> Result<IbcEvent, ChannelError> {
        let dst_msgs = self.build_chan_open_try()?;

        let events = self
            .dst_chain()
            .send_msgs(dst_msgs)
            .map_err(|e| ChannelError::SubmitError(self.dst_chain().id(), e))?;

        // Find the relevant event for channel open try
        let result = events
            .into_iter()
            .find(|event| {
                matches!(event, IbcEvent::OpenTryChannel(_))
                    || matches!(event, IbcEvent::ChainError(_))
            })
            .ok_or_else(|| {
                ChannelError::Failed("no chan try event was in the response".to_string())
            })?;

        match result {
            IbcEvent::OpenTryChannel(_) => Ok(result),
            IbcEvent::ChainError(e) => {
                Err(ChannelError::Failed(format!("tx response error: {}", e)))
            }
            _ => panic!("internal error"),
        }
    }

    pub fn build_chan_open_ack(&self) -> Result<Vec<Any>, ChannelError> {
        // Check that the destination chain will accept the message
        let _dst_expected_channel = self.validated_expected_channel(ChannelMsgType::OpenAck)?;

        let _src_channel = self
            .src_chain()
            .query_channel(self.src_port_id(), self.src_channel_id(), Height::default())
            .map_err(|e| ChannelError::QueryError(self.src_chain().id(), e))?;

        // Retrieve the connection
        let _dst_connection = self
            .dst_chain()
            .query_connection(self.dst_connection_id(), Height::default())
            .map_err(|e| ChannelError::QueryError(self.dst_chain().id(), e))?;

        let query_height = self
            .src_chain()
            .query_latest_height()
            .map_err(|e| ChannelError::QueryError(self.src_chain().id(), e))?;

        let proofs = self
            .src_chain()
            .build_channel_proofs(self.src_port_id(), self.src_channel_id(), query_height)
            .map_err(|e| {
                ChannelError::Failed(format!(
                    "failed while building the channel proofs at ACK step with error: {}",
                    e
                ))
            })?;

        // Build message(s) to update client on destination
        let mut msgs = self.build_update_client_on_dst(proofs.height())?;

        // Get signer
        let signer = self.dst_chain().get_signer().map_err(|e| {
            ChannelError::Failed(format!(
                "failed while fetching the signer for dst chain ({}) with error: {}",
                self.dst_chain().id(),
                e
            ))
        })?;

        // Build the domain type message
        let new_msg = MsgChannelOpenAck {
            port_id: self.dst_port_id().clone(),
            channel_id: self.dst_channel_id().clone(),
            counterparty_channel_id: self.src_channel_id().clone(),
            counterparty_version: self.src_version()?,
            proofs,
            signer,
        };

        msgs.push(new_msg.to_any());
        Ok(msgs)
    }

    pub fn build_chan_open_ack_and_send(&self) -> Result<IbcEvent, ChannelError> {
        let dst_msgs = self.build_chan_open_ack()?;

        let events = self
            .dst_chain()
            .send_msgs(dst_msgs)
            .map_err(|e| ChannelError::SubmitError(self.dst_chain().id(), e))?;

        // Find the relevant event for channel open ack
        let result = events
            .into_iter()
            .find(|event| {
                matches!(event, IbcEvent::OpenAckChannel(_))
                    || matches!(event, IbcEvent::ChainError(_))
            })
            .ok_or_else(|| {
                ChannelError::Failed("no chan ack event was in the response".to_string())
            })?;

        match result {
            IbcEvent::OpenAckChannel(_) => Ok(result),
            IbcEvent::ChainError(e) => {
                Err(ChannelError::Failed(format!("tx response error: {}", e)))
            }
            _ => panic!("internal error"),
        }
    }

    pub fn build_chan_open_confirm(&self) -> Result<Vec<Any>, ChannelError> {
        // Check that the destination chain will accept the message
        let _dst_expected_channel = self.validated_expected_channel(ChannelMsgType::OpenConfirm)?;

        let _src_channel = self
            .src_chain()
            .query_channel(self.src_port_id(), self.src_channel_id(), Height::default())
            .map_err(|e| ChannelError::QueryError(self.src_chain().id(), e))?;

        // Retrieve the connection
        let _dst_connection = self
            .dst_chain()
            .query_connection(self.dst_connection_id(), Height::default())
            .map_err(|e| ChannelError::QueryError(self.dst_chain().id(), e))?;

        let query_height = self
            .src_chain()
            .query_latest_height()
            .map_err(|e| ChannelError::QueryError(self.src_chain().id(), e))?;

        let proofs = self
            .src_chain()
            .build_channel_proofs(self.src_port_id(), self.src_channel_id(), query_height)
            .map_err(|e| ChannelError::Failed(format!("failed to build channel proofs: {}", e)))?;

        // Build message(s) to update client on destination
        let mut msgs = self.build_update_client_on_dst(proofs.height())?;

        // Get signer
        let signer = self.dst_chain().get_signer().map_err(|e| {
            ChannelError::Failed(format!(
                "failed while fetching the signer for dst chain ({}) with error: {}",
                self.dst_chain().id(),
                e
            ))
        })?;

        // Build the domain type message
        let new_msg = MsgChannelOpenConfirm {
            port_id: self.dst_port_id().clone(),
            channel_id: self.dst_channel_id().clone(),
            proofs,
            signer,
        };

        msgs.push(new_msg.to_any());
        Ok(msgs)
    }

    pub fn build_chan_open_confirm_and_send(&self) -> Result<IbcEvent, ChannelError> {
        let dst_msgs = self.build_chan_open_confirm()?;

        let events = self
            .dst_chain()
            .send_msgs(dst_msgs)
            .map_err(|e| ChannelError::SubmitError(self.dst_chain().id(), e))?;

        // Find the relevant event for channel open confirm
        let result = events
            .into_iter()
            .find(|event| {
                matches!(event, IbcEvent::OpenConfirmChannel(_))
                    || matches!(event, IbcEvent::ChainError(_))
            })
            .ok_or_else(|| {
                ChannelError::Failed("no chan confirm event was in the response".to_string())
            })?;

        match result {
            IbcEvent::OpenConfirmChannel(_) => Ok(result),
            IbcEvent::ChainError(e) => {
                Err(ChannelError::Failed(format!("tx response error: {}", e)))
            }
            _ => panic!("internal error"),
        }
    }

    pub fn build_chan_close_init(&self) -> Result<Vec<Any>, ChannelError> {
        let _channel = self
            .dst_chain()
            .query_channel(self.dst_port_id(), self.dst_channel_id(), Height::default())
            .map_err(|e| ChannelError::QueryError(self.dst_chain().id(), e))?;

        let signer = self.dst_chain().get_signer().map_err(|e| {
            ChannelError::Failed(format!(
                "failed while fetching the signer for dst chain ({}) with error: {}",
                self.dst_chain().id(),
                e
            ))
        })?;

        // Build the domain type message
        let new_msg = MsgChannelCloseInit {
            port_id: self.dst_port_id().clone(),
            channel_id: self.dst_channel_id().clone(),
            signer,
        };

        Ok(vec![new_msg.to_any()])
    }

    pub fn build_chan_close_init_and_send(&self) -> Result<IbcEvent, ChannelError> {
        let dst_msgs = self.build_chan_close_init()?;

        let events = self
            .dst_chain()
            .send_msgs(dst_msgs)
            .map_err(|e| ChannelError::SubmitError(self.dst_chain().id(), e))?;

        // Find the relevant event for channel close init
        let result = events
            .into_iter()
            .find(|event| {
                matches!(event, IbcEvent::CloseInitChannel(_))
                    || matches!(event, IbcEvent::ChainError(_))
            })
            .ok_or_else(|| {
                ChannelError::Failed("no chan init event was in the response".to_string())
            })?;

        match result {
            IbcEvent::CloseInitChannel(_) => Ok(result),
            IbcEvent::ChainError(e) => Err(ChannelError::Failed(format!(
                "tx response event consists of an error: {}",
                e
            ))),
            _ => panic!("internal error"),
        }
    }

    pub fn build_chan_close_confirm(&self) -> Result<Vec<Any>, ChannelError> {
        // Check that the destination chain will accept the message
        let _dst_expected_channel =
            self.validated_expected_channel(ChannelMsgType::CloseConfirm)?;

        let _src_channel = self
            .src_chain()
            .query_channel(self.src_port_id(), self.src_channel_id(), Height::default())
            .map_err(|e| ChannelError::QueryError(self.src_chain().id(), e))?;

        // Retrieve the connection
        let _dst_connection = self
            .dst_chain()
            .query_connection(self.dst_connection_id(), Height::default())
            .map_err(|e| ChannelError::QueryError(self.dst_chain().id(), e))?;

        let query_height = self
            .src_chain()
            .query_latest_height()
            .map_err(|e| ChannelError::QueryError(self.src_chain().id(), e))?;

        let proofs = self
            .src_chain()
            .build_channel_proofs(self.src_port_id(), self.src_channel_id(), query_height)
            .map_err(|e| ChannelError::Failed(format!("failed to build channel proofs: {}", e)))?;

        // Build message(s) to update client on destination
        let mut msgs = self.build_update_client_on_dst(proofs.height())?;

        // Get signer
        let signer = self.dst_chain().get_signer().map_err(|e| {
            ChannelError::Failed(format!(
                "failed while fetching the signer for dst chain ({}) with error: {}",
                self.dst_chain().id(),
                e
            ))
        })?;

        // Build the domain type message
        let new_msg = MsgChannelCloseConfirm {
            port_id: self.dst_port_id().clone(),
            channel_id: self.dst_channel_id().clone(),
            proofs,
            signer,
        };

        msgs.push(new_msg.to_any());
        Ok(msgs)
    }

    pub fn build_chan_close_confirm_and_send(&self) -> Result<IbcEvent, ChannelError> {
        let dst_msgs = self.build_chan_close_confirm()?;

        let events = self
            .dst_chain()
            .send_msgs(dst_msgs)
            .map_err(|e| ChannelError::SubmitError(self.dst_chain().id(), e))?;

        // Find the relevant event for channel close confirm
        let result = events
            .into_iter()
            .find(|event| {
                matches!(event, IbcEvent::CloseConfirmChannel(_))
                    || matches!(event, IbcEvent::ChainError(_))
            })
            .ok_or_else(|| {
                ChannelError::Failed("no chan confirm event was in the response".to_string())
            })?;

        match result {
            IbcEvent::CloseConfirmChannel(_) => Ok(result),
            IbcEvent::ChainError(e) => {
                Err(ChannelError::Failed(format!("tx response error: {}", e)))
            }
            _ => panic!("internal error"),
        }
    }
}

fn extract_channel_id(event: &IbcEvent) -> Result<&ChannelId, ChannelError> {
    match event {
        IbcEvent::OpenInitChannel(ev) => ev.channel_id().as_ref(),
        IbcEvent::OpenTryChannel(ev) => ev.channel_id().as_ref(),
        IbcEvent::OpenAckChannel(ev) => ev.channel_id().as_ref(),
        IbcEvent::OpenConfirmChannel(ev) => ev.channel_id().as_ref(),
        _ => None,
    }
    .ok_or_else(|| ChannelError::Failed("cannot extract channel_id from result".to_string()))
}

/// Enumeration of proof carrying ICS4 message, helper for relayer.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ChannelMsgType {
    OpenTry,
    OpenAck,
    OpenConfirm,
    CloseConfirm,
}

fn check_destination_channel_state(
    channel_id: ChannelId,
    existing_channel: ChannelEnd,
    expected_channel: ChannelEnd,
) -> Result<(), ChannelError> {
    let good_connection_hops =
        existing_channel.connection_hops() == expected_channel.connection_hops();

    // TODO: Refactor into a method
    let good_state = *existing_channel.state() as u32 <= *expected_channel.state() as u32;
    let good_channel_ids = existing_channel.counterparty().channel_id().is_none()
        || existing_channel.counterparty().channel_id()
            == expected_channel.counterparty().channel_id();

    // TODO: Check versions

    if good_state && good_connection_hops && good_channel_ids {
        Ok(())
    } else {
        Err(ChannelError::Failed(format!(
            "channel {} already exist in an incompatible state",
            channel_id
        )))
    }
}
