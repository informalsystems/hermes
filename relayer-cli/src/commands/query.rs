//! `query` subcommand

use abscissa_core::{Command, Options, Runnable};

mod channel;
mod client;
mod connection;
mod packet;

/// `query` subcommand
#[derive(Command, Debug, Options, Runnable)]
pub enum QueryCmd {
    /// The `query client` subcommand
    #[options(help = "query client")]
    Client(QueryClientCmds),

    /// The `query connection` subcommand
    #[options(help = "query connection")]
    Connection(QueryConnectionCmds),

    /// The `query channel` subcommand
    #[options(help = "query channel")]
    Channel(QueryChannelCmds),

    /// The `query packet` subcommand
    #[options(help = "query packets")]
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

    /// The `query clients` subcommand
    #[options(help = "query client all")]
    All(client::QueryAllClientsCmd),
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
