use ibc_relayer::chain::handle::BaseChainHandle;
use ibc_relayer_all_in_one::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_cosmos::contexts::chain::CosmosChain;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;

use crate::context::chain::MockSolomachineChainContext;
use crate::types::batch::CosmosBatchSender;
use crate::types::chain::SolomachineChainWrapper;

pub struct SolomachineRelay {
    pub runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
    pub src_chain: OfaChainWrapper<SolomachineChainWrapper<MockSolomachineChainContext>>,
    pub dst_chain: OfaChainWrapper<CosmosChain<BaseChainHandle>>,
    pub src_client_id: ClientId,
    pub dst_client_id: ClientId,
    //pub src_chain_message_batch_sender: SolomachineBatchSender,
    pub dst_chain_message_batch_sender: CosmosBatchSender,
}

impl SolomachineRelay {
    pub fn new(
        runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
        src_chain: OfaChainWrapper<SolomachineChainWrapper<MockSolomachineChainContext>>,
        dst_chain: OfaChainWrapper<CosmosChain<BaseChainHandle>>,
        src_client_id: ClientId,
        dst_client_id: ClientId,
        //src_chain_message_batch_sender: SolomachineBatchSender,
        dst_chain_message_batch_sender: CosmosBatchSender,
    ) -> Self {
        Self {
            runtime,
            src_chain,
            dst_chain,
            src_client_id,
            dst_client_id,
            //src_chain_message_batch_sender,
            dst_chain_message_batch_sender,
        }
    }
}
