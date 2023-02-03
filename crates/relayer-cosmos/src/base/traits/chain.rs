use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::{BaseChainHandle, ChainHandle};
use ibc_relayer::keyring::Secp256k1KeyPair;
use ibc_relayer_framework::base::core::traits::sync::Async;
use ibc_relayer_types::signer::Signer;
use tendermint_rpc::Url;

pub trait CosmosChain: Async {
    type Preset;

    type ChainHandle: ChainHandle;

    fn chain_handle(&self) -> &Self::ChainHandle;

    fn signer(&self) -> &Signer;

    fn tx_config(&self) -> &TxConfig;

    fn websocket_url(&self) -> &Url;

    fn key_entry(&self) -> &Secp256k1KeyPair;
}
