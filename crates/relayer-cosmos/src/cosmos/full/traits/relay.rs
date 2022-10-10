use ibc_relayer::config::filter::PacketFilter;

use crate::cosmos::base::traits::relay::CosmosRelay;

pub trait CosmosFullRelay: CosmosRelay {
    fn packet_filter(&self) -> &PacketFilter;
}
