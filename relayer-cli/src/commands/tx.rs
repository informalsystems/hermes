//! `tx` subcommand
use abscissa_core::{Command, Help, Options, Runnable};

use crate::commands::tx::client::{TxCreateClientCmd, TxUpdateClientCmd};

mod channel;
mod client;
mod connection;
mod packet;
mod transfer;

/// `tx` subcommand
#[derive(Command, Debug, Options, Runnable)]
pub enum TxCmd {
    /// The `help` subcommand
    #[options(help = "get usage information")]
    Help(Help<Self>),

    /// The `tx raw` subcommand
    #[options(help = "tx raw")]
    Raw(TxRawCommands),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum TxRawCommands {
    /// The `help` subcommand
    #[options(help = "get usage information")]
    Help(Help<Self>),

    /// The `tx raw create-client` subcommand submits a MsgCreateClient in a transaction to a chain
    #[options(help = "tx raw create-client")]
    CreateClient(TxCreateClientCmd),

    /// The `tx raw update-client` subcommand submits a MsgUpdateClient in a transaction to a chain
    #[options(help = "tx raw update-client")]
    UpdateClient(TxUpdateClientCmd),

    /// The `tx raw conn-init` subcommand
    #[options(help = "tx raw conn-init")]
    ConnInit(connection::TxRawConnInitCmd),

    /// The `tx raw conn-try` subcommand
    #[options(help = "tx raw conn-try")]
    ConnTry(connection::TxRawConnTryCmd),

    /// The `tx raw conn-ack` subcommand
    #[options(help = "tx raw conn-ack")]
    ConnAck(connection::TxRawConnAckCmd),

    /// The `tx raw conn-confirm` subcommand
    #[options(help = "tx raw conn-confirm")]
    ConnConfirm(connection::TxRawConnConfirmCmd),

    /// The `tx raw chan-init` subcommand
    #[options(help = "tx raw chan-init")]
    ChanInit(channel::TxRawChanInitCmd),

    /// The `tx raw chan-try` subcommand
    #[options(help = "tx raw chan-try")]
    ChanTry(channel::TxRawChanTryCmd),

    /// The `tx raw chan-ack` subcommand
    #[options(help = "tx raw chan-ack")]
    ChanAck(channel::TxRawChanAckCmd),

    /// The `tx raw chan-confirm` subcommand
    #[options(help = "tx raw chan-confirm")]
    ChanConfirm(channel::TxRawChanConfirmCmd),

    /// The `tx raw packet-send` subcommand
    #[options(help = "tx raw packet-send")]
    PacketSend(transfer::TxRawSendPacketCmd),

    /// The `tx raw packet-recv` subcommand
    #[options(help = "tx raw packet-recv")]
    PacketRecv(packet::TxRawPacketRecvCmd),

    /// The `tx raw packet-ack` subcommand
    #[options(help = "tx raw packet-ack")]
    PacketAck(packet::TxRawPacketAckCmd),
}
