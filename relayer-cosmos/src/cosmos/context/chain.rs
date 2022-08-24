use ibc::signer::Signer;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::keyring::KeyEntry;
use ibc_relayer_framework::one_for_all::traits::batch::OfaBatchContext;
use ibc_relayer_framework::one_for_all::traits::runtime::OfaRuntimeContext;
use tendermint::abci::responses::Event;
use tokio::sync::{mpsc, oneshot};

use crate::cosmos::context::runtime::CosmosRuntimeContext;
use crate::cosmos::error::Error;
use crate::cosmos::message::CosmosIbcMessage;

#[derive(Clone)]
pub struct CosmosChainContext<Handle> {
    pub handle: Handle,
    pub signer: Signer,
    pub tx_config: TxConfig,
    pub key_entry: KeyEntry,
    pub runtime: OfaRuntimeContext<CosmosRuntimeContext>,
    pub batch: OfaBatchContext<Self, CosmosRuntimeContext>,
    pub batch_sender: mpsc::Sender<(
        Vec<CosmosIbcMessage>,
        oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
    )>,
}

impl<Handle> CosmosChainContext<Handle> {
    pub fn new(
        runtime: CosmosRuntimeContext,
        handle: Handle,
        signer: Signer,
        tx_config: TxConfig,
        key_entry: KeyEntry,
    ) -> (
        Self,
        mpsc::Receiver<(
            Vec<CosmosIbcMessage>,
            oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
        )>,
    ) {
        let batch = OfaBatchContext::new(runtime.clone());
        let runtime = OfaRuntimeContext::new(runtime);
        let (batch_sender, receiver) = mpsc::channel(1024);

        let chain = Self {
            handle,
            signer,
            tx_config,
            key_entry,
            runtime,
            batch,
            batch_sender,
        };

        (chain, receiver)
    }
}
