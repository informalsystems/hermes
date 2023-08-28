use basecoin_app::modules::ibc::IbcContext;
use basecoin_store::impls::RevertibleStore;
use ibc::core::events::IbcEvent;
use ibc::core::timestamp::Timestamp;
use ibc::core::ValidationContext;
use ibc::Any;
use ibc::Height;

use std::sync::Arc;
use std::sync::Mutex;

use super::runtime::MockClock;
use crate::contexts::runtime::MockRuntimeContext;
use crate::traits::endpoint::BasecoinEndpoint;
use crate::types::error::Error;
use crate::types::status::ChainStatus;
use crate::util::mutex::MutexUtil;

#[derive(Clone)]
pub struct MockCosmosContext<Endpoint: BasecoinEndpoint> {
    /// Chain handle
    pub querier: Arc<Endpoint>,
    /// Current chain status
    pub current_status: Arc<Mutex<ChainStatus>>,
    /// Chain runtime
    pub runtime: MockRuntimeContext,
}

impl<Endpoint: BasecoinEndpoint> MockCosmosContext<Endpoint> {
    /// Constructs a new mock cosmos chain instance.
    pub fn new(querier: Arc<Endpoint>, clock: Arc<MockClock>) -> Self {
        let runtime = MockRuntimeContext::new(clock.clone());

        let current_status = Arc::new(Mutex::new(ChainStatus::new(
            Height::new(querier.get_chain_id().revision_number(), 1).expect("never fails"),
            clock.get_timestamp(),
        )));

        Self {
            querier,
            current_status,
            runtime,
        }
    }

    pub fn runtime(&self) -> &MockRuntimeContext {
        &self.runtime
    }

    pub fn ibc_context(
        &self,
    ) -> IbcContext<RevertibleStore<<Endpoint as BasecoinEndpoint>::Store>> {
        self.ibc().ctx()
    }

    pub fn get_current_timestamp(&self) -> Timestamp {
        self.current_status.acquire_mutex().timestamp
    }

    pub fn get_current_height(&self) -> Height {
        self.current_status.acquire_mutex().height
    }

    pub fn subscribe(&self) {
        let ctx = self.clone();
        tokio::spawn(async move {
            let mut blocks_len = 1;
            loop {
                tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;

                if ctx.get_blocks().len() > blocks_len {
                    let current_time = ctx.ibc_context().host_timestamp().unwrap();

                    let current_height = ctx.ibc_context().host_height().unwrap();

                    ctx.runtime.clock.set_timestamp(current_time);

                    let current_status = ChainStatus::new(current_height, current_time);

                    let mut last_status = ctx.current_status.acquire_mutex();

                    *last_status = current_status;

                    blocks_len = ctx.get_blocks().len();
                }
            }
        });
    }

    pub fn submit_messages(&self, msgs: Vec<Any>) -> Result<Vec<Vec<IbcEvent>>, Error> {
        let mut events = Vec::new();

        self.ibc_context().host_height()?;

        for msg in msgs {
            let ibc_events = self.ibc().process_message(msg)?;

            events.push(ibc_events);
        }

        Ok(events)
    }
}
