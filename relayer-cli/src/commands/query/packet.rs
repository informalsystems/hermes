use abscissa_core::{Clap, Command, Runnable};

mod ack;
mod acks;
mod commitment;
mod commitments;
mod unreceived_acks;
mod unreceived_packets;

#[derive(Command, Debug, Clap, Runnable)]
pub enum QueryPacketCmds {
    /// The `query packet commitments` subcommand
    #[clap(about = "Query packet commitments")]
    Commitments(commitments::QueryPacketCommitmentsCmd),

    /// The `query packet commitment` subcommand
    #[clap(about = "Query packet commitment")]
    Commitment(commitment::QueryPacketCommitmentCmd),

    /// The `query packet acks` subcommand
    #[clap(about = "Query packet acknowledgments")]
    Acks(acks::QueryPacketAcknowledgementsCmd),

    /// The `query packet ack` subcommand
    #[clap(about = "Query packet acknowledgment")]
    Ack(ack::QueryPacketAcknowledgmentCmd),

    /// The `query packet unreceived-packets` subcommand
    #[clap(about = "Query unreceived packets")]
    UnreceivedPackets(unreceived_packets::QueryUnreceivedPacketsCmd),

    /// The `query packet unreceived-acks` subcommand
    #[clap(about = "Query unreceived acknowledgments")]
    UnreceivedAcks(unreceived_acks::QueryUnreceivedAcknowledgementCmd),
}
