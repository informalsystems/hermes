use ibc::clients::ics07_tendermint::client_type;
use ibc::core::ics24_host::identifier::ClientId;
use ibc::core::ValidationContext;
use ibc_relayer_components::relay::traits::packet_relayer::CanRelayPacket;
use std::sync::Arc;
use tokio::task::JoinHandle;

use crate::traits::handle::BasecoinHandle;
use crate::types::error::Error;
use crate::util::msgs::build_transfer_packet;

use super::chain::MockCosmosContext;
use super::runtime::{MockClock, MockRuntimeContext};

#[derive(Clone)]
pub struct MockCosmosRelay<SrcChain: BasecoinHandle, DstChain: BasecoinHandle> {
    pub src_chain: Arc<MockCosmosContext<SrcChain>>,
    pub dst_chain: Arc<MockCosmosContext<DstChain>>,
    pub src_client_id: ClientId,
    pub dst_client_id: ClientId,
    pub runtime: MockRuntimeContext,
}

impl<SrcChain, DstChain> MockCosmosRelay<SrcChain, DstChain>
where
    SrcChain: BasecoinHandle,
    DstChain: BasecoinHandle,
{
    pub fn new(
        src_chain: Arc<MockCosmosContext<SrcChain>>,
        dst_chain: Arc<MockCosmosContext<DstChain>>,
        clock: Arc<MockClock>,
    ) -> Result<MockCosmosRelay<SrcChain, DstChain>, Error> {
        let src_client_counter = src_chain.ibc_context().client_counter()?;

        let src_client_id = ClientId::new(client_type(), src_client_counter)?;

        let dst_client_counter = dst_chain.ibc_context().client_counter()?;

        let dst_client_id = ClientId::new(client_type(), dst_client_counter)?;

        let runtime = MockRuntimeContext { clock };

        Ok(Self {
            src_chain,
            dst_chain,
            src_client_id,
            dst_client_id,
            runtime,
        })
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

    pub fn spawn(&mut self) -> JoinHandle<()> {
        let packet = build_transfer_packet(1);

        let relayer = self.clone();

        tokio::spawn(async move {
            relayer.relay_packet(&packet).await.unwrap();
        })
    }
}
