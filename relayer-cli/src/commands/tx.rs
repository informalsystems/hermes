//! `tx` subcommand
use abscissa_core::{config::Override, Clap, Command, Runnable};
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
#[derive(Command, Debug, Clap, Runnable)]
pub enum TxCmd {
    /// The `tx raw` subcommand
    #[clap(
        subcommand,
        about = "Raw commands for sending transactions to a configured chain."
    )]
    Raw(TxRawCommands),
}

#[derive(Command, Debug, Clap, Runnable)]
pub enum TxRawCommands {
    /// The `tx raw create-client` subcommand submits a MsgCreateClient in a transaction to a chain
    #[clap(about = "Create a client for source chain on destination chain")]
    CreateClient(TxCreateClientCmd),

    /// The `tx raw update-client` subcommand submits a MsgUpdateClient in a transaction to a chain
    #[clap(about = "Update the specified client on destination chain")]
    UpdateClient(TxUpdateClientCmd),

    /// The `tx raw upgrade-client` subcommand. Submits a MsgUpgradeClient in a transaction to a chain.
    #[clap(about = "Upgrade the specified client on destination chain")]
    UpgradeClient(TxUpgradeClientCmd),

    /// The `tx raw upgrade-clients` subcommand. Submits a MsgUpgradeClient in a transaction to multiple chains.
    #[clap(about = "Upgrade all IBC clients that target a specific chain")]
    UpgradeClients(TxUpgradeClientsCmd),

    /// The `tx raw conn-init` subcommand
    #[clap(about = "Initialize a connection (ConnectionOpenInit)")]
    ConnInit(connection::TxRawConnInitCmd),

    /// The `tx raw conn-try` subcommand
    #[clap(about = "Relay the connection attempt (ConnectionOpenTry)")]
    ConnTry(connection::TxRawConnTryCmd),

    /// The `tx raw conn-ack` subcommand
    #[clap(about = "Relay acknowledgment of a connection attempt (ConnectionOpenAck)")]
    ConnAck(connection::TxRawConnAckCmd),

    /// The `tx raw conn-confirm` subcommand
    #[clap(about = "Confirm opening of a connection (ConnectionOpenConfirm)")]
    ConnConfirm(connection::TxRawConnConfirmCmd),

    /// The `tx raw chan-open-init` subcommand
    #[clap(about = "Initialize a channel (ChannelOpenInit)")]
    ChanOpenInit(channel::TxRawChanOpenInitCmd),

    /// The `tx raw chan-try` subcommand
    #[clap(about = "Relay the channel attempt (ChannelOpenTry)")]
    ChanOpenTry(channel::TxRawChanOpenTryCmd),

    /// The `tx raw chan-open-ack` subcommand
    #[clap(about = "Relay acknowledgment of a channel attempt (ChannelOpenAck)")]
    ChanOpenAck(channel::TxRawChanOpenAckCmd),

    /// The `tx raw chan-open-confirm` subcommand
    #[clap(about = "Confirm opening of a channel (ChannelOpenConfirm)")]
    ChanOpenConfirm(channel::TxRawChanOpenConfirmCmd),

    /// The `tx raw chan-close-init` subcommand
    #[clap(about = "Initiate the closing of a channel (ChannelCloseInit)")]
    ChanCloseInit(channel::TxRawChanCloseInitCmd),

    /// The `tx raw chan-close-confirm` subcommand
    #[clap(about = "Confirm the closing of a channel (ChannelCloseConfirm)")]
    ChanCloseConfirm(channel::TxRawChanCloseConfirmCmd),

    /// The `tx raw packet-send` subcommand
    #[clap(about = "Send a fungible token transfer test transaction (ICS20 MsgTransfer)")]
    FtTransfer(transfer::TxIcs20MsgTransferCmd),

    /// The `tx raw packet-recv` subcommand
    #[clap(about = "Relay receive or timeout packets")]
    PacketRecv(packet::TxRawPacketRecvCmd),

    /// The `tx raw packet-ack` subcommand
    #[clap(about = "Relay acknowledgment packets")]
    PacketAck(packet::TxRawPacketAckCmd),

    /// The `tx raw upgrade-chain` subcommand
    #[clap(about = "Send an IBC upgrade plan")]
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
