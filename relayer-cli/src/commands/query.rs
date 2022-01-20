//! `query` subcommand

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use crate::commands::query::channel_ends::QueryChannelEndsCmd;
use crate::commands::query::channels::QueryChannelsCmd;
use crate::commands::query::packet::QueryPacketCmds;

mod channel;
mod channel_ends;
mod channels;
mod client;
mod clients;
mod connection;
mod connections;
mod packet;
mod tx;

/// `query` subcommand
#[derive(Command, Debug, Parser, Runnable)]
pub enum QueryCmd {
    /// Query information about clients
    #[clap(subcommand)]
    Client(QueryClientCmds),

    /// Query the identifiers of all clients on a chain
    Clients(clients::QueryAllClientsCmd),

    /// Query information about connections
    #[clap(subcommand)]
    Connection(QueryConnectionCmds),

    /// Query the identifiers of all connections on a chain
    Connections(connections::QueryConnectionsCmd),

    /// Query information about channels
    #[clap(subcommand)]
    Channel(QueryChannelCmds),

    /// Query the identifiers of all channels on a given chain
    Channels(QueryChannelsCmd),

    /// Query information about packets
    #[clap(subcommand)]
    Packet(QueryPacketCmds),

    /// Query information about transactions
    #[clap(subcommand)]
    Tx(tx::QueryTxCmd),
}

#[derive(Command, Debug, Parser, Runnable)]
pub enum QueryClientCmds {
    /// Query the client full state
    State(client::QueryClientStateCmd),

    /// Query the client consensus state
    Consensus(client::QueryClientConsensusCmd),

    /// Query for the header used in a client update at a certain height
    Header(client::QueryClientHeaderCmd),

    /// Query the client connections
    Connections(client::QueryClientConnectionsCmd),
}

#[derive(Command, Debug, Parser, Runnable)]
pub enum QueryConnectionCmds {
    /// Query connection end
    End(connection::QueryConnectionEndCmd),

    /// Query connection channels
    Channels(connection::QueryConnectionChannelsCmd),
}

#[derive(Command, Debug, Parser, Runnable)]
pub enum QueryChannelCmds {
    /// Query channel end
    End(channel::QueryChannelEndCmd),

    /// Query channel ends and underlying connection and client objects
    Ends(QueryChannelEndsCmd),
}
