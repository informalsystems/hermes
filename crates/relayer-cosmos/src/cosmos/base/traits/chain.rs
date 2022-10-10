use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::keyring::KeyEntry;
use ibc_relayer_framework::base::traits::core::Async;
use ibc_relayer_framework::full::one_for_all::traits::telemetry::OfaTelemetryWrapper;
use ibc_relayer_types::signer::Signer;

use crate::cosmos::base::types::batch::CosmosBatchChannel;
use crate::cosmos::base::types::telemetry::CosmosTelemetry;

pub trait CosmosChain: Async {
    type Components;

    type ChainHandle: ChainHandle;

    fn chain_handle(&self) -> &Self::ChainHandle;

    fn signer(&self) -> &Signer;

    fn tx_config(&self) -> &TxConfig;

    fn key_entry(&self) -> &KeyEntry;
}

pub trait CosmosFullChain: CosmosChain {
    fn batch_channel(&self) -> &CosmosBatchChannel;

    fn telemetry(&self) -> &OfaTelemetryWrapper<CosmosTelemetry>;
}
