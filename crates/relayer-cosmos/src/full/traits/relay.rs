use ibc_relayer::config::filter::PacketFilter;

use crate::base::traits::relay::CosmosRelay;
use crate::full::types::batch::{CosmosBatchReceiver, CosmosBatchSender};

pub trait CosmosFullRelay: CosmosRelay {
    fn packet_filter(&self) -> &PacketFilter;

    fn src_chain_message_batch_sender(&self) -> &CosmosBatchSender;

    fn src_chain_message_batch_receiver(&self) -> &CosmosBatchReceiver;

    fn dst_chain_message_batch_sender(&self) -> &CosmosBatchSender;

    fn dst_chain_message_batch_receiver(&self) -> &CosmosBatchReceiver;
}
