//! `query` subcommand

use crate::commands::query::channels::QueryChannelsCmd;
use abscissa_core::{Command, Options, Runnable};

mod channel;
mod channels;
mod client;
mod connection;
mod connections;
mod packet;

/// `query` subcommand
#[derive(Command, Debug, Options, Runnable)]
pub enum QueryCmd {
    /// The `query client` subcommand
    #[options(help = "query information about client(s)")]
    Client(QueryClientCmds),

    /// The `query connection` subcommand
    #[options(help = "query information about connection(s)")]
    Connection(QueryConnectionCmds),

    /// The `query connections` subcommand
    #[options(help = "query the identifiers of all connection on a chain")]
    Connections(connections::QueryConnectionsCmd),

    /// The `query channel` subcommand
    #[options(help = "query information about channel(s)")]
    Channel(QueryChannelCmds),

    /// The `query channels` subcommand
    #[options(help = "query the identifiers of all channels on a given chain")]
    Channels(QueryChannelsCmd),

    /// The `query packet` subcommand
    #[options(help = "query information about packet(s)")]
    Packet(QueryPacketCmds),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryClientCmds {
    /// The `query client state` subcommand
    #[options(help = "query client full state")]
    State(client::QueryClientStateCmd),

    /// The `query client consensus` subcommand
    #[options(help = "query client consensus")]
    Consensus(client::QueryClientConsensusCmd),

    /// The `query client connections` subcommand
    #[options(help = "query client connections")]
    Connections(client::QueryClientConnectionsCmd),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryConnectionCmds {
    /// The `query connection end` subcommand
    #[options(help = "query connection end")]
    End(connection::QueryConnectionEndCmd),

    /// The `query connection channels` subcommand
    #[options(help = "query connection channels")]
    Channels(connection::QueryConnectionChannelsCmd),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryChannelCmds {
    /// The `query channel end` subcommand
    #[options(help = "query channel end")]
    End(channel::QueryChannelEndCmd),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryPacketCmds {
    /// The `query packet commitments` subcommand
    #[options(help = "query packet commitments")]
    Commitments(packet::QueryPacketCommitmentsCmd),

    /// The `query packet commitment` subcommand
    #[options(help = "query packet commitment")]
    Commitment(packet::QueryPacketCommitmentCmd),

    /// The `query packet unreceived-packets` subcommand
    #[options(help = "query packet unreceived-packets")]
    UnreceivedPackets(packet::QueryUnreceivedPacketsCmd),

    /// The `query packet acks` subcommand
    #[options(help = "query packet acks")]
    Acks(packet::QueryPacketAcknowledgementsCmd),

    /// The `query packet ack` subcommand
    #[options(help = "query packet ack")]
    Ack(packet::QueryPacketAcknowledgmentCmd),

    /// The `query packet unreceived-acks` subcommand
    #[options(help = "query packet unreceived-acks")]
    UnreceivedAcks(packet::QueryUnreceivedAcknowledgementCmd),
}
