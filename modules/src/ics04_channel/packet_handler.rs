pub mod send_packet;

#[derive(Clone, Debug)]
pub struct PacketResult {
    pub send_seq_number: u64,
    //pub commitment: CommitmentPrefix;
}
