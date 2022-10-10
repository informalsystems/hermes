use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::keyring::KeyEntry;
use ibc_relayer_framework::base::traits::core::Async;
use ibc_relayer_types::signer::Signer;

pub trait CosmosChain: Async {
    type Components;

    type ChainHandle: ChainHandle;

    fn chain_handle(&self) -> &Self::ChainHandle;

    fn signer(&self) -> &Signer;

    fn tx_config(&self) -> &TxConfig;

    fn key_entry(&self) -> &KeyEntry;
}
