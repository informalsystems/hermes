use ibc_relayer_all_in_one::one_for_all::traits::chain::OfaIbcChain;
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;

pub struct SolomachineRelay<SrcChain, DstChain>
where
    SrcChain: OfaIbcChain<DstChain>,
    DstChain: OfaIbcChain<SrcChain>,
{
    pub runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
    pub src_chain: SrcChain,
    pub dst_chain: DstChain,
    pub src_client_id: ClientId,
    pub dst_client_id: ClientId,
}
