use core::fmt;

use serde::Serialize;

use ibc_relayer::util::collate::{Collated, CollatedIterExt};
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::Height;

pub use ibc_relayer::chain::counterparty::PendingPackets;

#[derive(Serialize)]
pub struct CollatedPendingPackets {
    pub unreceived_packets: Vec<Collated<Sequence>>,
    pub unreceived_acks: Vec<Collated<Sequence>>,
}

impl fmt::Debug for CollatedPendingPackets {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PendingPackets")
            .field("unreceived_packets", &self.unreceived_packets)
            .field("unreceived_acks", &self.unreceived_acks)
            .finish()
    }
}

impl CollatedPendingPackets {
    pub fn new(pending: PendingPackets) -> Self {
        Self {
            unreceived_packets: pending.unreceived_packets.into_iter().collated().collect(),
            unreceived_acks: pending.unreceived_acks.into_iter().collated().collect(),
        }
    }
}

#[derive(Serialize, Debug)]
pub struct PacketSeqs {
    pub height: Height,
    pub seqs: Vec<Sequence>,
}

impl PacketSeqs {
    pub fn collated(self) -> CollatedPacketSeqs {
        CollatedPacketSeqs {
            height: self.height,
            seqs: self.seqs.into_iter().collated().collect(),
        }
    }
}

#[derive(Serialize)]
pub struct CollatedPacketSeqs {
    pub height: Height,
    pub seqs: Vec<Collated<Sequence>>,
}

impl fmt::Debug for CollatedPacketSeqs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PacketSeqs")
            .field("height", &self.height)
            .field("seqs", &self.seqs)
            .finish()
    }
}
