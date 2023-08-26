use alloc::sync::Arc;
use ibc::core::ics24_host::identifier::ChainId;
use ibc_relayer_components::relay::traits::packet_relayer::CanRelayPacket;
use tokio::task::JoinHandle;

use super::chain::MockCosmosChain;
use super::relay::MockCosmosRelay;
use super::runtime::MockClock;
use super::runtime::MockRuntimeContext;
use crate::traits::handler::ChainHandler;
use crate::util::msgs::build_transfer_packet;

pub struct MockCosmosBuilder {
    pub chains: Vec<Arc<MockCosmosChain>>,
    pub relayers: Vec<Arc<MockCosmosRelay>>,
    pub handlers: Vec<JoinHandle<()>>,
    pub runtime: MockRuntimeContext,
}

impl MockCosmosBuilder {
    pub fn new(clock: Arc<MockClock>) -> Self {
        Self {
            chains: Vec::new(),
            relayers: Vec::new(),
            handlers: Vec::new(),
            runtime: MockRuntimeContext { clock },
        }
    }

    pub fn new_default() -> Self {
        Self::new(Arc::new(MockClock::default()))
    }

    pub fn build_chain(&mut self, chain_id: ChainId) -> Arc<MockCosmosChain> {
        let chain = Arc::new(MockCosmosChain::new(chain_id, self.runtime.clock.clone()));

        self.chains.push(chain.clone());

        chain
    }

    pub fn build_relayer(
        &mut self,
        src_chain: Arc<MockCosmosChain>,
        dst_chain: Arc<MockCosmosChain>,
    ) -> MockCosmosRelay {
        let relayer = MockCosmosRelay::new(src_chain, dst_chain, self.runtime.clone())
            .expect("failed to build relayer");

        self.relayers.push(Arc::new(relayer.clone()));

        relayer
    }

    pub fn spawn_chains(&mut self) {
        for c in self.chains.clone() {
            let c_clone = c.clone();

            let handle = tokio::spawn(async move {
                c_clone.run().await;
            });

            self.handlers.push(handle);
        }
    }

    pub async fn relay_packet(&mut self) {
        for r in &self.relayers {
            let packet = build_transfer_packet(1);

            let relayer_clone = r.clone();

            let handle = tokio::spawn(async move {
                relayer_clone.relay_packet(&packet).await.unwrap();
            });

            self.handlers.push(handle);
        }
    }

    pub fn stop(&self) {
        for h in &self.handlers {
            h.abort();
        }
    }
}
