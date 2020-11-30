use std::str::FromStr;
use std::time::SystemTime;

use prost_types::Any;
use thiserror::Error;

use ibc_proto::ibc::core::channel::v1::MsgChannelOpenAck as RawMsgChannelOpenAck;
use ibc_proto::ibc::core::channel::v1::MsgChannelOpenConfirm as RawMsgChannelOpenConfirm;
use ibc_proto::ibc::core::channel::v1::MsgChannelOpenInit as RawMsgChannelOpenInit;
use ibc_proto::ibc::core::channel::v1::MsgChannelOpenTry as RawMsgChannelOpenTry;

use ibc::ics04_channel::channel::{ChannelEnd, Counterparty, Order, State};
use ibc::ics04_channel::msgs::chan_open_ack::MsgChannelOpenAck;
use ibc::ics04_channel::msgs::chan_open_confirm::MsgChannelOpenConfirm;
use ibc::ics04_channel::msgs::chan_open_init::MsgChannelOpenInit;
use ibc::ics04_channel::msgs::chan_open_try::MsgChannelOpenTry;
use ibc::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use ibc::tx_msg::Msg;
use ibc::Height;

use crate::chain::handle::ChainHandle;
use crate::config::RelayPath;
use crate::connection::{Connection, ConnectionConfig};
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
    connection_id: ConnectionId,
    client_id: ClientId,
    port_id: PortId,
    channel_id: ChannelId,
}

impl ChannelConfigSide {
    pub fn new(
        chain_id: &ChainId,
        connection_id: &ConnectionId,
        client_id: &ClientId,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> ChannelConfigSide {
        Self {
            chain_id: chain_id.clone(),
            connection_id: connection_id.clone(),
            client_id: client_id.clone(),
            port_id: port_id.clone(),
            channel_id: channel_id.clone(),
        }
    }

    pub fn chain_id(&self) -> &ChainId {
        &self.chain_id
    }

    pub fn connection_id(&self) -> &ConnectionId {
        &self.connection_id
    }

    pub fn client_id(&self) -> &ClientId {
        &self.client_id
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
}

impl ChannelConfig {
    pub fn new(conn: &ConnectionConfig, path: &RelayPath) -> Result<ChannelConfig, String> {
        let a_config = ChannelConfigSide {
            chain_id: conn.a_end().chain_id().clone(),
            connection_id: conn.a_end().connection_id().clone(),
            client_id: conn.a_end().client_id().clone(),
            port_id: PortId::from_str(path.a_port.clone().ok_or("Port id not specified")?.as_str())
                .map_err(|e| format!("Invalid port id ({:?})", e))?,
            channel_id: ChannelId::from_str(
                path.a_channel
                    .clone()
                    .ok_or("Channel id not specified")?
                    .as_str(),
            )
            .map_err(|e| format!("Invalid channel id ({:?})", e))?,
        };

        let b_config = ChannelConfigSide {
            chain_id: conn.b_end().chain_id().clone(),
            connection_id: conn.b_end().connection_id().clone(),
            client_id: conn.b_end().client_id().clone(),
            port_id: PortId::from_str(
                path.b_port
                    .clone()
                    .ok_or("Counterparty port id not specified")?
                    .as_str(),
            )
            .map_err(|e| format!("Invalid counterparty port id ({:?})", e))?,
            channel_id: ChannelId::from_str(
                path.b_channel
                    .clone()
                    .ok_or("Counterparty channel id not specified")?
                    .as_str(),
            )
            .map_err(|e| format!("Invalid counterparty channel id ({:?})", e))?,
        };

        Ok(ChannelConfig {
            ordering: Default::default(), // TODO - add to config
            a_config,
            b_config,
        })
    }
}

// temp fix for queries
fn get_channel(
    chain: impl ChainHandle,
    port: &PortId,
    id: &ChannelId,
) -> Result<Option<ChannelEnd>, ChannelError> {
    match chain.query_channel(port, id, Height::zero()) {
        Err(e) => match e.kind() {
            Kind::EmptyResponseValue => Ok(None),
            _ => Err(ChannelError::Failed(format!(
                "error retrieving channel {:?}",
                e
            ))),
        },
        Ok(chan) => Ok(Some(chan)),
    }
}

impl Channel {
    pub fn new(
        a_chain: impl ChainHandle,
        b_chain: impl ChainHandle,
        _connection: Connection,
        config: ChannelConfig,
    ) -> Result<Channel, ChannelError> {
        let done = '\u{1F973}';

        let flipped = config.flipped();

        let mut counter = 0;

        while counter < MAX_ITER {
            counter += 1;
            let now = SystemTime::now();

            // Continue loop if query error
            let a_channel = get_channel(
                a_chain.clone(),
                &config.a_end().port_id,
                &config.a_end().channel_id,
            );
            if a_channel.is_err() {
                continue;
            }
            let b_channel = get_channel(
                b_chain.clone(),
                &config.b_end().port_id,
                &config.b_end().channel_id,
            );
            if b_channel.is_err() {
                continue;
            }

            match (a_channel?, b_channel?) {
                (None, None) => {
                    // Init to src
                    match build_chan_init_and_send(a_chain.clone(), b_chain.clone(), &flipped) {
                        Err(e) => println!("{:?} Failed ChanInit {:?}", e, config.a_end()),
                        Ok(_) => println!("{}  ChanInit {:?}", done, config.a_end()),
                    }
                }
                (Some(a_channel), None) => {
                    // Try to dest
                    assert!(a_channel.state_matches(&State::Init));
                    match build_chan_try_and_send(b_chain.clone(), a_chain.clone(), &config) {
                        Err(e) => println!("{:?} Failed ChanTry {:?}", e, config.b_end()),
                        Ok(_) => println!("{}  ChanTry {:?}", done, config.b_end()),
                    }
                }
                (None, Some(b_channel)) => {
                    // Try to src
                    assert!(b_channel.state_matches(&State::Init));
                    match build_chan_try_and_send(a_chain.clone(), b_chain.clone(), &flipped) {
                        Err(e) => println!("{:?} Failed ChanTry {:?}", e, config.a_end()),
                        Ok(_) => println!("{}  ChanTry {:?}", done, config.a_end()),
                    }
                }
                (Some(a_channel), Some(b_channel)) => {
                    match (a_channel.state(), b_channel.state()) {
                        (&State::Init, &State::Init) => {
                            // Try to dest
                            // Try to dest
                            match build_chan_try_and_send(b_chain.clone(), a_chain.clone(), &config)
                            {
                                Err(e) => println!("{:?} Failed ChanTry {:?}", e, config.b_end()),
                                Ok(_) => println!("{}  ChanTry {:?}", done, config.b_end()),
                            }
                        }
                        (&State::TryOpen, &State::Init) => {
                            // Ack to dest
                            match build_chan_ack_and_send(b_chain.clone(), a_chain.clone(), &config)
                            {
                                Err(e) => println!("{:?} Failed ChanAck {:?}", e, config.b_end()),
                                Ok(_) => println!("{}  ChanAck {:?}", done, config.b_end()),
                            }
                        }
                        (&State::Init, &State::TryOpen) | (&State::TryOpen, &State::TryOpen) => {
                            // Ack to src
                            match build_chan_ack_and_send(
                                a_chain.clone(),
                                b_chain.clone(),
                                &flipped,
                            ) {
                                Err(e) => println!("{:?} Failed ChanAck {:?}", e, config.a_end()),
                                Ok(_) => println!("{}  ChanAck {:?}", done, config.a_end()),
                            }
                        }
                        (&State::Open, &State::TryOpen) => {
                            // Confirm to dest
                            match build_chan_confirm_and_send(
                                b_chain.clone(),
                                a_chain.clone(),
                                &config,
                            ) {
                                Err(e) => {
                                    println!("{:?} Failed ChanConfirm {:?}", e, config.b_end())
                                }
                                Ok(_) => println!("{}  ChanConfirm {:?}", done, config.b_end()),
                            }
                        }
                        (&State::TryOpen, &State::Open) => {
                            // Confirm to src
                            match build_chan_confirm_and_send(
                                a_chain.clone(),
                                b_chain.clone(),
                                &flipped,
                            ) {
                                Err(e) => println!("{:?} ChanConfirm {:?}", e, flipped),
                                Ok(_) => println!("{}  ChanConfirm {:?}", done, flipped),
                            }
                        }
                        (&State::Open, &State::Open) => {
                            println!(
                                "{}  {}  {}  Channel handshake finished for {:#?}",
                                done, done, done, config
                            );
                            return Ok(Channel { config });
                        }
                        _ => {} // TODO channel close
                    }
                }
            }
            println!("elapsed time {:?}\n", now.elapsed().unwrap().as_secs());
        }

        Err(ChannelError::Failed(format!(
            "Failed to finish channel handshake in {:?} iterations",
            MAX_ITER
        )))
    }
}

/// Enumeration of proof carrying ICS4 message, helper for relayer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChannelMsgType {
    OpenTry,
    OpenAck,
    OpenConfirm,
}

pub fn build_chan_init(
    dst_chain: impl ChainHandle,
    _src_chain: impl ChainHandle,
    opts: &ChannelConfig,
) -> Result<Vec<Any>, Error> {
    // Check that the destination chain will accept the message, i.e. it does not have the channel
    if dst_chain
        .query_channel(
            opts.dst().port_id(),
            opts.dst().channel_id(),
            Height::default(),
        )
        .is_ok()
    {
        return Err(Kind::ChanOpenInit(
            opts.dst().channel_id().clone(),
            "channel already exist".into(),
        )
        .into());
    }

    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    let counterparty = Counterparty::new(
        opts.src().port_id().clone(),
        Some(opts.src().channel_id().clone()),
    );

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
        channel_id: opts.dst().channel_id().clone(),
        channel,
        signer,
    };

    Ok(vec![new_msg.to_any::<RawMsgChannelOpenInit>()])
}

pub fn build_chan_init_and_send(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    opts: &ChannelConfig,
) -> Result<String, Error> {
    let dst_msgs = build_chan_init(dst_chain.clone(), src_chain, &opts)?;
    Ok(dst_chain.send_tx(dst_msgs)?)
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
    opts: &ChannelConfig,
) -> Result<ChannelEnd, Error> {
    // If there is a channel present on the destination chain, it should look like this:
    let counterparty = Counterparty::new(
        opts.src().port_id().clone(),
        Option::from(opts.src().channel_id().clone()),
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
        vec![opts.dst().connection_id().clone()],
        dst_chain.module_version(&opts.dst().port_id())?,
    );

    // Retrieve existing channel if any
    let dest_channel = dst_chain.query_channel(
        &opts.dst().port_id(),
        &opts.dst().channel_id(),
        Height::default(),
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
                opts.src().channel_id().clone(),
                "missing channel on source chain".to_string(),
            )
            .into());
        }
    }

    check_destination_channel_state(
        opts.dst().channel_id().clone(),
        dest_channel?,
        dest_expected_channel.clone(),
    )?;

    Ok(dest_expected_channel)
}

pub fn build_chan_try(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    opts: &ChannelConfig,
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
            opts.src().channel_id().clone(),
            "try options inconsistent with existing channel on destination chain".to_string(),
        )
        .context(e)
    })?;

    let src_channel = src_chain
        .query_channel(
            &opts.src().port_id(),
            &opts.src().channel_id(),
            Height::default(),
        )
        .map_err(|e| {
            Kind::ChanOpenTry(
                opts.dst().channel_id().clone(),
                "channel does not exist on source".into(),
            )
            .context(e)
        })?;

    // Retrieve the connection
    let dest_connection =
        dst_chain.query_connection(&opts.dst().connection_id().clone(), Height::default())?;

    let ics_target_height = src_chain.query_latest_height()?;

    // Build message to update client on destination
    let mut msgs = build_update_client(
        dst_chain.clone(),
        src_chain.clone(),
        &dest_connection.client_id(),
        ics_target_height,
    )?;

    let counterparty = Counterparty::new(
        opts.src().port_id().clone(),
        Some(opts.src().channel_id().clone()),
    );

    let channel = ChannelEnd::new(
        State::Init,
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
        channel_id: opts.dst().channel_id().clone(),
        counterparty_chosen_channel_id: src_channel.counterparty().channel_id,
        channel,
        counterparty_version: src_chain.module_version(&opts.src().port_id())?,
        proofs: src_chain.build_channel_proofs(
            &opts.src().port_id(),
            &opts.src().channel_id(),
            ics_target_height,
        )?,
        signer,
    };

    let mut new_msgs = vec![new_msg.to_any::<RawMsgChannelOpenTry>()];

    msgs.append(&mut new_msgs);

    Ok(msgs)
}

pub fn build_chan_try_and_send(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    opts: &ChannelConfig,
) -> Result<String, Error> {
    let dst_msgs = build_chan_try(dst_chain.clone(), src_chain, &opts)?;
    Ok(dst_chain.send_tx(dst_msgs)?)
}

pub fn build_chan_ack(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    opts: &ChannelConfig,
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
    let dest_connection =
        dst_chain.query_connection(&opts.dst().connection_id().clone(), Height::default())?;

    let ics_target_height = src_chain.query_latest_height()?;

    // Build message to update client on destination
    let mut msgs = build_update_client(
        dst_chain.clone(),
        src_chain.clone(),
        &dest_connection.client_id(),
        ics_target_height,
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
        proofs: src_chain.build_channel_proofs(
            &opts.src().port_id(),
            &opts.src().channel_id(),
            ics_target_height,
        )?,
        signer,
    };

    let mut new_msgs = vec![new_msg.to_any::<RawMsgChannelOpenAck>()];

    msgs.append(&mut new_msgs);

    Ok(msgs)
}

pub fn build_chan_ack_and_send(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    opts: &ChannelConfig,
) -> Result<String, Error> {
    let dst_msgs = build_chan_ack(dst_chain.clone(), src_chain, &opts)?;
    Ok(dst_chain.send_tx(dst_msgs)?)
}

pub fn build_chan_confirm(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    opts: &ChannelConfig,
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
    let dest_connection =
        dst_chain.query_connection(&opts.dst().connection_id().clone(), Height::default())?;

    let ics_target_height = src_chain.query_latest_height()?;

    // Build message to update client on destination
    let mut msgs = build_update_client(
        dst_chain.clone(),
        src_chain.clone(),
        &dest_connection.client_id(),
        ics_target_height,
    )?;

    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    // Build the domain type message
    let new_msg = MsgChannelOpenConfirm {
        port_id: opts.dst().port_id().clone(),
        channel_id: opts.dst().channel_id().clone(),
        proofs: src_chain.build_channel_proofs(
            &opts.src().port_id(),
            &opts.src().channel_id(),
            ics_target_height,
        )?,
        signer,
    };

    let mut new_msgs = vec![new_msg.to_any::<RawMsgChannelOpenConfirm>()];

    msgs.append(&mut new_msgs);

    Ok(msgs)
}

pub fn build_chan_confirm_and_send(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    opts: &ChannelConfig,
) -> Result<String, Error> {
    let dst_msgs = build_chan_confirm(dst_chain.clone(), src_chain, &opts)?;
    Ok(dst_chain.send_tx(dst_msgs)?)
}
