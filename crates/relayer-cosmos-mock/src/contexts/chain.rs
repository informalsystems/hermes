use basecoin_app::modules::ibc::IbcContext;
use basecoin_store::impls::RevertibleStore;
use ibc::core::events::IbcEvent;
use ibc::core::timestamp::Timestamp;
use ibc::core::ValidationContext;
use ibc::Any;
use ibc::Height;
use ibc_relayer_components::runtime::traits::sleep::CanSleep;
use ibc_relayer_components_extra::runtime::traits::spawn::Spawner;
use ibc_relayer_components_extra::runtime::traits::spawn::TaskHandle;
use ibc_relayer_runtime::types::runtime::TokioRuntimeContext;

use std::sync::Arc;
use std::sync::Mutex;

use crate::traits::endpoint::BasecoinEndpoint;
use crate::types::error::Error;
use crate::types::status::ChainStatus;
use crate::util::mutex::MutexUtil;

/// Holds the necessary fields for querying a mock Cosmos
/// chain endpoint.
#[derive(Clone)]
pub struct MockCosmosContext<Endpoint: BasecoinEndpoint> {
    /// Chain runtime
    pub runtime: TokioRuntimeContext,
    /// Chain handle
    pub querier: Arc<Endpoint>,
    /// Current chain status
    pub current_status: Arc<Mutex<ChainStatus>>,
}

impl<Endpoint: BasecoinEndpoint> MockCosmosContext<Endpoint> {
    /// Constructs a new mock cosmos chain instance.
    pub fn new(runtime: TokioRuntimeContext, querier: Arc<Endpoint>) -> Self {
        let current_status = Arc::new(Mutex::new(ChainStatus::new(
            Height::new(querier.get_chain_id().revision_number(), 1).expect("never fails"),
            Timestamp::now(),
        )));

        Self {
            runtime,
            querier,
            current_status,
        }
    }

    pub fn runtime(&self) -> &TokioRuntimeContext {
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

    /// Keeps the chain context updated by continuously tracking the latest generated block.
    pub fn sync(&self) -> Box<dyn TaskHandle> {
        let ctx = self.clone();
        self.runtime().spawn(async move {
            let mut blocks_len = 1;
            loop {
                ctx.runtime()
                    .sleep(tokio::time::Duration::from_millis(200))
                    .await;

                if ctx.get_blocks().len() <= blocks_len {
                    continue;
                }

                let current_timestamp = ctx.ibc_context().host_timestamp().unwrap();

                let current_height = ctx.ibc_context().host_height().unwrap();

                let current_status = ChainStatus::new(current_height, current_timestamp);

                let mut last_status = ctx.current_status.acquire_mutex();

                *last_status = current_status;

                blocks_len = ctx.get_blocks().len();
            }
        })
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
