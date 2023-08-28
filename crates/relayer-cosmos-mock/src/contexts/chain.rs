use basecoin_app::modules::ibc::IbcContext;
use basecoin_store::impls::RevertibleStore;
use ibc::core::events::IbcEvent;
use ibc::core::timestamp::Timestamp;
use ibc::Any;
use ibc::Height;

use std::sync::Arc;
use std::sync::Mutex;

use super::runtime::MockClock;
use crate::contexts::runtime::MockRuntimeContext;
use crate::traits::endpoint::Endpoint;
use crate::traits::handle::BasecoinHandle;
use crate::types::error::Error;
use crate::types::status::ChainStatus;
use crate::util::mutex::MutexUtil;

#[derive(Clone)]
pub struct MockCosmosContext<Handle: BasecoinHandle> {
    /// Chain handle
    pub handle: Arc<Handle>,
    /// Current chain status
    pub current_status: Arc<Mutex<ChainStatus>>,
    /// Chain runtime
    pub runtime: MockRuntimeContext,
}

impl<Handle: BasecoinHandle> MockCosmosContext<Handle> {
    /// Constructs a new mock cosmos chain instance.
    pub fn new(handle: Arc<Handle>, clock: Arc<MockClock>) -> Self {
        let runtime = MockRuntimeContext::new(clock.clone());

        let current_status = Arc::new(Mutex::new(ChainStatus::new(
            Height::new(handle.chain_id().revision_number(), 1).expect("never fails"),
            clock.get_timestamp(),
        )));

        Self {
            handle,
            current_status,
            runtime,
        }
    }

    pub fn runtime(&self) -> &MockRuntimeContext {
        &self.runtime
    }

    pub fn ibc_context(&self) -> IbcContext<RevertibleStore<<Handle as BasecoinHandle>::Store>> {
        self.handle.ibc().ctx()
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

                if ctx.handle.blocks().len() > blocks_len {
                    let current_time = ctx.query_current_timestamp().unwrap();

                    let current_height = ctx.query_current_height().unwrap();

                    ctx.runtime.clock.set_timestamp(current_time);

                    let current_status = ChainStatus::new(current_height, current_time);

                    let mut last_status = ctx.current_status.acquire_mutex();

                    *last_status = current_status;

                    blocks_len = ctx.handle.blocks().len();
                }
            }
        });
    }

    pub fn submit_messages(&self, msgs: Vec<Any>) -> Result<Vec<Vec<IbcEvent>>, Error> {
        let mut events = Vec::new();

        for msg in msgs {
            let ibc_events = self.handle.ibc().process_message(msg)?;

            events.push(ibc_events);
        }

        Ok(events)
    }
}
