//! `tx` subcommand
use abscissa_core::{config::Override, Command, Help, Options, Runnable};
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
#[derive(Command, Debug, Options, Runnable)]
pub enum TxCmd {
    /// The `help` subcommand
    #[options(help = "Get usage information")]
    Help(Help<Self>),

    /// The `tx raw` subcommand
    #[options(help = "Raw commands for sending transactions to a configured chain.")]
    Raw(TxRawCommands),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum TxRawCommands {
    /// The `help` subcommand
    #[options(help = "Get usage information")]
    Help(Help<Self>),

    /// The `tx raw create-client` subcommand submits a MsgCreateClient in a transaction to a chain
    #[options(help = "Create a client for source chain on destination chain")]
    CreateClient(TxCreateClientCmd),

    /// The `tx raw update-client` subcommand submits a MsgUpdateClient in a transaction to a chain
    #[options(help = "Update the specified client on destination chain")]
    UpdateClient(TxUpdateClientCmd),

    /// The `tx raw upgrade-client` subcommand. Submits a MsgUpgradeClient in a transaction to a chain.
    #[options(help = "Upgrade the specified client on destination chain")]
    UpgradeClient(TxUpgradeClientCmd),

    /// The `tx raw upgrade-clients` subcommand. Submits a MsgUpgradeClient in a transaction to multiple chains.
    #[options(help = "Upgrade all IBC clients that target a specific chain")]
    UpgradeClients(TxUpgradeClientsCmd),

    /// The `tx raw conn-init` subcommand
    #[options(help = "Initialize a connection (ConnectionOpenInit)")]
    ConnInit(connection::TxRawConnInitCmd),

    /// The `tx raw conn-try` subcommand
    #[options(help = "Relay the connection attempt (ConnectionOpenTry)")]
    ConnTry(connection::TxRawConnTryCmd),

    /// The `tx raw conn-ack` subcommand
    #[options(help = "Relay acknowledgment of a connection attempt (ConnectionOpenAck)")]
    ConnAck(connection::TxRawConnAckCmd),

    /// The `tx raw conn-confirm` subcommand
    #[options(help = "Confirm opening of a connection (ConnectionOpenConfirm)")]
    ConnConfirm(connection::TxRawConnConfirmCmd),

    /// The `tx raw chan-open-init` subcommand
    #[options(help = "Initialize a channel (ChannelOpenInit)")]
    ChanOpenInit(channel::TxRawChanOpenInitCmd),

    /// The `tx raw chan-try` subcommand
    #[options(help = "Relay the channel attempt (ChannelOpenTry)")]
    ChanOpenTry(channel::TxRawChanOpenTryCmd),

    /// The `tx raw chan-open-ack` subcommand
    #[options(help = "Relay acknowledgment of a channel attempt (ChannelOpenAck)")]
    ChanOpenAck(channel::TxRawChanOpenAckCmd),

    /// The `tx raw chan-open-confirm` subcommand
    #[options(help = "Confirm opening of a channel (ChannelOpenConfirm)")]
    ChanOpenConfirm(channel::TxRawChanOpenConfirmCmd),

    /// The `tx raw chan-close-init` subcommand
    #[options(help = "Initiate the closing of a channel (ChannelCloseInit)")]
    ChanCloseInit(channel::TxRawChanCloseInitCmd),

    /// The `tx raw chan-close-confirm` subcommand
    #[options(help = "Confirm the closing of a channel (ChannelCloseConfirm)")]
    ChanCloseConfirm(channel::TxRawChanCloseConfirmCmd),

    /// The `tx raw packet-send` subcommand
    #[options(help = "Send a fungible token transfer test transaction (ICS20 MsgTransfer)")]
    FtTransfer(transfer::TxIcs20MsgTransferCmd),

    /// The `tx raw packet-recv` subcommand
    #[options(help = "Relay receive or timeout packets")]
    PacketRecv(packet::TxRawPacketRecvCmd),

    /// The `tx raw packet-ack` subcommand
    #[options(help = "Relay acknowledgment packets")]
    PacketAck(packet::TxRawPacketAckCmd),

    /// The `tx raw upgrade-chain` subcommand
    #[options(help = "Send an IBC upgrade plan")]
    UpgradeChain(upgrade::TxIbcUpgradeChainCmd),
}

impl Override<Config> for TxCmd {
    fn override_config(&self, config: Config) -> Result<Config, abscissa_core::FrameworkError> {
        match self {
            Self::Raw(cmd) => cmd.override_config(config),
            _ => Ok(config),
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
