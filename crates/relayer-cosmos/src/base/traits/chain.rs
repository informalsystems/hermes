use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::keyring::Secp256k1KeyPair;
use ibc_relayer_all_in_one::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_types::signer::Signer;
use tendermint_rpc::client::CompatMode;
use tendermint_rpc::{HttpClient, WebSocketClientUrl};

pub trait CosmosChain: Async {
    type Preset: Async;

    type ChainHandle: ChainHandle;

    fn runtime(&self) -> &OfaRuntimeWrapper<TokioRuntimeContext>;

    fn chain_handle(&self) -> &Self::ChainHandle;

    fn signer(&self) -> &Signer;

    fn tx_config(&self) -> &TxConfig;

    fn rpc_client(&self) -> &HttpClient;

    fn compat_mode(&self) -> &CompatMode;

    fn websocket_url(&self) -> &WebSocketClientUrl;

    fn key_entry(&self) -> &Secp256k1KeyPair;
}
