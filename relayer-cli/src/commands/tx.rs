//! `tx` subcommand
use abscissa_core::clap::Parser;
use abscissa_core::{config::Override, Command, Runnable};
use ibc_relayer::config::Config;

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
    /// Initialize a connection (ConnectionOpenInit)
    ConnInit(connection::TxConnInitCmd),

    /// Relay the connection attempt (ConnectionOpenTry)
    ConnTry(connection::TxConnTryCmd),

    /// Relay acknowledgment of a connection attempt (ConnectionOpenAck)
    ConnAck(connection::TxConnAckCmd),

    /// Confirm opening of a connection (ConnectionOpenConfirm)
    ConnConfirm(connection::TxConnConfirmCmd),

    /// Initialize a channel (ChannelOpenInit)
    ChanOpenInit(channel::TxChanOpenInitCmd),

    /// Relay the channel attempt (ChannelOpenTry)
    ChanOpenTry(channel::TxChanOpenTryCmd),

    /// Relay acknowledgment of a channel attempt (ChannelOpenAck)
    ChanOpenAck(channel::TxChanOpenAckCmd),

    /// Confirm opening of a channel (ChannelOpenConfirm)
    ChanOpenConfirm(channel::TxChanOpenConfirmCmd),

    /// Initiate the closing of a channel (ChannelCloseInit)
    ChanCloseInit(channel::TxChanCloseInitCmd),

    /// Confirm the closing of a channel (ChannelCloseConfirm)
    ChanCloseConfirm(channel::TxChanCloseConfirmCmd),

    /// Send a fungible token transfer test transaction (ICS20 MsgTransfer)
    FtTransfer(transfer::TxIcs20MsgTransferCmd),

    /// Relay receive or timeout packets
    PacketRecv(packet::TxPacketRecvCmd),

    /// Relay acknowledgment packets
    PacketAck(packet::TxPacketAckCmd),

    /// Send an IBC upgrade plan
    UpgradeChain(upgrade::TxIbcUpgradeChainCmd),
}

impl Override<Config> for TxCmd {
    fn override_config(&self, config: Config) -> Result<Config, abscissa_core::FrameworkError> {
        match self {
            Self::FtTransfer(cmd) => cmd.override_config(config),
            _ => Ok(config),
        }
    }
}
