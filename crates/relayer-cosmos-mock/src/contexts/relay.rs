use ibc::clients::ics07_tendermint::client_type;
use ibc::core::ics24_host::identifier::ClientId;
use ibc::core::ValidationContext;
use ibc_relayer_runtime::types::runtime::TokioRuntimeContext;
use std::sync::Arc;

use crate::traits::endpoint::BasecoinEndpoint;
use crate::types::error::Error;

use super::chain::MockCosmosContext;

/// The relay context for relaying between `BasecoinEndpoint`s.
///
/// The `SrcChain` and `DstChain` endpoints are wrapped in
/// `MockCosmosContext`, which bundles the `BasecoinEndpoint` with
/// the runtime.
#[derive(Clone)]
pub struct MockCosmosRelay<SrcChain, DstChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    pub runtime: TokioRuntimeContext,
    pub src_chain: Arc<MockCosmosContext<SrcChain>>,
    pub dst_chain: Arc<MockCosmosContext<DstChain>>,
    pub src_client_id: ClientId,
    pub dst_client_id: ClientId,
}

impl<SrcChain, DstChain> MockCosmosRelay<SrcChain, DstChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    pub fn new(
        runtime: TokioRuntimeContext,
        src_chain: Arc<MockCosmosContext<SrcChain>>,
        dst_chain: Arc<MockCosmosContext<DstChain>>,
    ) -> Result<MockCosmosRelay<SrcChain, DstChain>, Error> {
        let src_client_counter = src_chain.ibc_context().client_counter()?;

        let src_client_id = ClientId::new(client_type(), src_client_counter)?;

        let dst_client_counter = dst_chain.ibc_context().client_counter()?;

        let dst_client_id = ClientId::new(client_type(), dst_client_counter)?;

        Ok(Self {
            runtime,
            src_chain,
            dst_chain,
            src_client_id,
            dst_client_id,
        })
    }

    pub fn runtime(&self) -> &TokioRuntimeContext {
        &self.runtime
    }

    pub fn src_chain(&self) -> &Arc<MockCosmosContext<SrcChain>> {
        &self.src_chain
    }

    pub fn dst_chain(&self) -> &Arc<MockCosmosContext<DstChain>> {
        &self.dst_chain
    }

    pub fn src_client_id(&self) -> &ClientId {
        &self.src_client_id
    }

    pub fn dst_client_id(&self) -> &ClientId {
        &self.dst_client_id
    }
}
