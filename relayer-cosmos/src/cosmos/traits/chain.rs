use ibc::signer::Signer;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::keyring::KeyEntry;
use ibc_relayer_framework::core::traits::core::Async;
use ibc_relayer_framework::one_for_all::impls::message::OfaMessage;
use std::sync::Mutex;
use tendermint::abci::responses::Event;
use tokio::sync::{mpsc, oneshot};

use crate::cosmos::error::Error;
use crate::cosmos::types::chain::CosmosChainContext;

pub trait CosmosChain: Async {
    type Components;

    type ChainHandle: ChainHandle;

    fn chain_handle(&self) -> &Self::ChainHandle;

    fn signer(&self) -> &Signer;

    fn tx_config(&self) -> &TxConfig;

    fn key_entry(&self) -> &KeyEntry;
}

pub trait CosmosChainWithBatch: CosmosChain {
    fn batch_sender(
        &self,
    ) -> &mpsc::Sender<(
        Vec<OfaMessage<CosmosChainContext<Self>>>,
        oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
    )>;

    fn batch_receiver(
        &self,
    ) -> &Mutex<
        mpsc::Receiver<(
            Vec<OfaMessage<CosmosChainContext<Self>>>,
            oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
        )>,
    >;
}
