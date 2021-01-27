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

    /// The `tx raw chan-open-init` subcommand
    #[options(help = "tx raw chan-open-init")]
    ChanOpenInit(channel::TxRawChanOpenInitCmd),

    /// The `tx raw chan-try` subcommand
    #[options(help = "tx raw chan-open-try")]
    ChanOpenTry(channel::TxRawChanOpenTryCmd),

    /// The `tx raw chan-open-ack` subcommand
    #[options(help = "tx raw chan-open-ack")]
    ChanOpenAck(channel::TxRawChanOpenAckCmd),

    /// The `tx raw chan-open-confirm` subcommand
    #[options(help = "tx raw chan-open-confirm")]
    ChanOpenConfirm(channel::TxRawChanOpenConfirmCmd),

    /// The `tx raw chan-close-init` subcommand
    #[options(help = "tx raw chan-close-init")]
    ChanCloseInit(channel::TxRawChanCloseInitCmd),

    /// The `tx raw chan-close-confirm` subcommand
    #[options(help = "tx raw chan-close-confirm")]
    ChanCloseConfirm(channel::TxRawChanCloseConfirmCmd),

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
