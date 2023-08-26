use ibc::clients::ics07_tendermint::client_type;
use ibc::core::ics24_host::identifier::ClientId;
use ibc::core::ValidationContext;
use std::sync::Arc;

use crate::types::error::Error;

use super::chain::MockCosmosChain;
use super::runtime::MockRuntimeContext;

#[derive(Clone)]
pub struct MockCosmosRelay {
    pub src_chain: Arc<MockCosmosChain>,
    pub dst_chain: Arc<MockCosmosChain>,
    pub src_client_id: ClientId,
    pub dst_client_id: ClientId,
    pub runtime: MockRuntimeContext,
}

impl MockCosmosRelay {
    pub fn new(
        src_chain: Arc<MockCosmosChain>,
        dst_chain: Arc<MockCosmosChain>,
        runtime: MockRuntimeContext,
    ) -> Result<MockCosmosRelay, Error> {
        let src_client_counter = src_chain.ibc_context().client_counter()?;

        let src_client_id = ClientId::new(client_type(), src_client_counter)?;

        let dst_client_counter = dst_chain.ibc_context().client_counter()?;

        let dst_client_id = ClientId::new(client_type(), dst_client_counter)?;

        Ok(Self {
            src_chain,
            dst_chain,
            src_client_id,
            dst_client_id,
            runtime,
        })
    }

    pub fn src_chain(&self) -> &Arc<MockCosmosChain> {
        &self.src_chain
    }

    pub fn dst_chain(&self) -> &Arc<MockCosmosChain> {
        &self.dst_chain
    }

    pub fn src_client_id(&self) -> &ClientId {
        &self.src_client_id
    }

    pub fn dst_client_id(&self) -> &ClientId {
        &self.dst_client_id
    }
}
