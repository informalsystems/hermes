use basecoin_app::modules::auth::Auth;
use basecoin_app::modules::bank::Bank;
use basecoin_app::modules::context::prefix;
use basecoin_app::modules::context::Identifiable;
use basecoin_app::modules::ibc::Ibc;
use basecoin_app::modules::ibc::IbcContext;
use basecoin_app::{BaseCoinApp, Builder};
use basecoin_store::impls::InMemoryStore;
use basecoin_store::impls::RevertibleStore;

use ibc::clients::ics07_tendermint::client_state::AllowUpdate;
use ibc::clients::ics07_tendermint::client_state::ClientState;
use ibc::core::ics02_client::msgs::create_client::MsgCreateClient;
use ibc::core::ics24_host::identifier::ChainId;
use ibc::core::timestamp::Timestamp;
use ibc::core::Msg;
use ibc::Any;
use ibc::Height;

use tendermint::time::Time;
use tendermint_testgen::light_block::TmLightBlock;
use tendermint_testgen::Generator;
use tendermint_testgen::LightBlock;

use std::sync::Arc;
use std::sync::Mutex;
use std::time::Duration;

use super::runtime::MockClock;
use crate::contexts::runtime::MockRuntimeContext;
use crate::traits::endpoint::Endpoint;
use crate::types::error::Error;
use crate::types::status::ChainStatus;
use crate::util::dummy::dummy_signer;
use crate::util::mutex::MutexUtil;

#[derive(Clone)]
pub struct MockCosmosChain {
    /// Chain identifier
    pub chain_id: ChainId,
    /// Current chain status
    pub current_status: Arc<Mutex<ChainStatus>>,
    /// Chain application
    pub app: BaseCoinApp<InMemoryStore>,
    /// Chain blocks
    pub blocks: Arc<Mutex<Vec<TmLightBlock>>>,
    /// Chain runtime
    pub runtime: MockRuntimeContext,
}

impl MockCosmosChain {
    /// Constructs a new mock cosmos chain instance.
    pub fn new(chain_id: ChainId, clock: Arc<MockClock>) -> Self {
        let app_builder = Builder::new(InMemoryStore::default());

        let auth = Auth::new(app_builder.module_store(&prefix::Auth {}.identifier()));
        let bank = Bank::new(
            app_builder.module_store(&prefix::Bank {}.identifier()),
            auth.account_reader().clone(),
            auth.account_keeper().clone(),
        );
        let ibc: Ibc<RevertibleStore<InMemoryStore>> = Ibc::new(
            app_builder.module_store(&prefix::Ibc {}.identifier()),
            bank.bank_keeper().clone(),
        );

        // register modules with the app
        let app = app_builder
            .add_module(prefix::Auth {}.identifier(), auth.clone())
            .add_module(prefix::Bank {}.identifier(), bank.clone())
            .add_module(prefix::Ibc {}.identifier(), ibc)
            .build();

        let runtime = MockRuntimeContext::new(clock.clone());

        let current_status = Arc::new(Mutex::new(ChainStatus::new(
            Height::new(chain_id.revision_number(), 1).expect("never fails"),
            Time::now().into(),
        )));

        let chain = Self {
            chain_id,
            current_status,
            app,
            blocks: Arc::new(Mutex::new(vec![])),
            runtime,
        };

        chain
    }

    pub fn chain_id(&self) -> &ChainId {
        &self.chain_id
    }

    pub fn runtime(&self) -> &MockRuntimeContext {
        &self.runtime
    }

    pub fn get_current_timestamp(&self) -> Timestamp {
        self.current_status.acquire_mutex().timestamp
    }

    pub fn get_current_height(&self) -> Height {
        self.current_status.acquire_mutex().height
    }

    pub fn ibc_context(&self) -> IbcContext<RevertibleStore<InMemoryStore>> {
        self.app.ibc().ctx()
    }

    pub fn grow_blocks(&self) {
        let mut blocks = self.blocks.acquire_mutex();

        let height = blocks.len() as u64 + 1;

        let current_time = Time::now();

        let tm_light_block = LightBlock::new_default_with_time_and_chain_id(
            self.chain_id.to_string(),
            current_time,
            height,
        )
        .generate()
        .expect("failed to generate light block");

        blocks.push(tm_light_block);

        self.runtime.clock.set_timestamp(current_time);

        let current_status = ChainStatus::new(
            Height::new(self.chain_id.revision_number(), height).expect("invalid height"),
            current_time.into(),
        );

        let mut last_status = self.current_status.acquire_mutex();

        *last_status = current_status;
    }

    pub async fn build_msg_create_client(&self) -> Result<Any, Error> {
        let tm_client_state = ClientState::new(
            self.chain_id.clone(),
            Default::default(),
            Duration::from_secs(64000),
            Duration::from_secs(128000),
            Duration::from_millis(3000),
            self.get_current_height(),
            Default::default(),
            Default::default(),
            AllowUpdate {
                after_expiry: false,
                after_misbehaviour: false,
            },
        )?;

        let current_height = self.get_current_height();

        let tm_consensus_state = self.query_host_consensus_state(&current_height)?;

        let msg_create_client = MsgCreateClient {
            client_state: tm_client_state.into(),
            consensus_state: tm_consensus_state.into(),
            signer: dummy_signer(),
        };

        Ok(msg_create_client.to_any())
    }
}
