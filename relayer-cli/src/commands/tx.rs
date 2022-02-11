//! `tx` subcommand
use abscissa_core::clap::Parser;
use abscissa_core::{config::Override, Command, Runnable};
use ibc_relayer::config::Config;

use crate::commands::tx::client::{
    TxCreateClientCmd, TxUpdateClientCmd, TxUpgradeClientCmd, TxUpgradeClientsCmd,
};

mod channel;
pub(crate) mod client;
mod connection;
mod packet;
mod transfer;
mod upgrade;

/// `tx` subcommand
#[allow(clippy::large_enum_variant)]
#[derive(Command, Debug, Parser, Runnable)]
pub enum TxCmd {
    /// Raw commands for sending transactions to a configured chain.
    #[clap(subcommand)]
    Raw(TxRawCommands),
}

#[derive(Command, Debug, Parser, Runnable)]
pub enum TxRawCommands {
    /// Create a client for source chain on destination chain
    CreateClient(TxCreateClientCmd),

    /// Update the specified client on destination chain
    UpdateClient(TxUpdateClientCmd),

    /// Upgrade the specified client on destination chain
    UpgradeClient(TxUpgradeClientCmd),

    /// Upgrade all IBC clients that target a specific chain
    UpgradeClients(TxUpgradeClientsCmd),

    /// Initialize a connection (ConnectionOpenInit)
    ConnInit(connection::TxRawConnInitCmd),

    /// Relay the connection attempt (ConnectionOpenTry)
    ConnTry(connection::TxRawConnTryCmd),

    /// Relay acknowledgment of a connection attempt (ConnectionOpenAck)
    ConnAck(connection::TxRawConnAckCmd),

    /// Confirm opening of a connection (ConnectionOpenConfirm)
    ConnConfirm(connection::TxRawConnConfirmCmd),

    /// Initialize a channel (ChannelOpenInit)
    ChanOpenInit(channel::TxRawChanOpenInitCmd),

    /// Relay the channel attempt (ChannelOpenTry)
    ChanOpenTry(channel::TxRawChanOpenTryCmd),

    /// Relay acknowledgment of a channel attempt (ChannelOpenAck)
    ChanOpenAck(channel::TxRawChanOpenAckCmd),

    /// Confirm opening of a channel (ChannelOpenConfirm)
    ChanOpenConfirm(channel::TxRawChanOpenConfirmCmd),

    /// Initiate the closing of a channel (ChannelCloseInit)
    ChanCloseInit(channel::TxRawChanCloseInitCmd),

    /// Confirm the closing of a channel (ChannelCloseConfirm)
    ChanCloseConfirm(channel::TxRawChanCloseConfirmCmd),

    /// Send a fungible token transfer test transaction (ICS20 MsgTransfer)
    FtTransfer(transfer::TxIcs20MsgTransferCmd),

    /// Relay receive or timeout packets
    PacketRecv(packet::TxRawPacketRecvCmd),

    /// Relay acknowledgment packets
    PacketAck(packet::TxRawPacketAckCmd),

    /// Send an IBC upgrade plan
    UpgradeChain(upgrade::TxIbcUpgradeChainCmd),
}

impl Override<Config> for TxCmd {
    fn override_config(&self, config: Config) -> Result<Config, abscissa_core::FrameworkError> {
        match self {
            Self::Raw(cmd) => cmd.override_config(config),
        }
    }
}

impl Override<Config> for TxRawCommands {
    fn override_config(&self, config: Config) -> Result<Config, abscissa_core::FrameworkError> {
        match self {
            Self::FtTransfer(cmd) => cmd.override_config(config),
            _ => Ok(config),
        }
    }
}
