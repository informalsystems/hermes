use std::fmt::Debug;
use std::sync::Arc;
use std::sync::Mutex;
use std::time::Duration;

use basecoin_app::modules::auth::Auth;
use basecoin_app::modules::bank::Bank;
use basecoin_app::modules::context::prefix;
use basecoin_app::modules::context::Identifiable;
use basecoin_app::modules::ibc::Ibc;
use basecoin_app::BaseCoinApp;
use basecoin_app::Builder;
use basecoin_store::context::ProvableStore;
use ibc::core::ics24_host::identifier::ChainId;
use tendermint::Time;
use tendermint_testgen::light_block::TmLightBlock;
use tendermint_testgen::Generator;
use tendermint_testgen::LightBlock;
use tokio::task::JoinHandle;

use crate::traits::handle::BasecoinHandle;
use crate::util::mutex::MutexUtil;

#[derive(Clone)]
pub struct MockBasecoin<S>
where
    S: ProvableStore + Debug,
{
    /// Chain identifier
    pub chain_id: ChainId,
    /// Chain application
    pub app: BaseCoinApp<S>,
    /// Chain blocks
    pub blocks: Arc<Mutex<Vec<TmLightBlock>>>,
}

impl<S: ProvableStore + Default + Debug> MockBasecoin<S> {
    /// Constructs a new mock cosmos chain instance.
    pub fn new(chain_id: ChainId, store: S) -> Self {
        let app_builder = Builder::new(store);

        let auth = Auth::new(app_builder.module_store(&prefix::Auth {}.identifier()));
        let bank = Bank::new(
            app_builder.module_store(&prefix::Bank {}.identifier()),
            auth.account_reader().clone(),
            auth.account_keeper().clone(),
        );
        let ibc = Ibc::new(
            app_builder.module_store(&prefix::Ibc {}.identifier()),
            bank.bank_keeper().clone(),
        );

        // register modules with the app
        let app = app_builder
            .add_module(prefix::Auth {}.identifier(), auth.clone())
            .add_module(prefix::Bank {}.identifier(), bank.clone())
            .add_module(prefix::Ibc {}.identifier(), ibc)
            .build();

        Self {
            chain_id,
            app,
            blocks: Arc::new(Mutex::new(vec![])),
        }
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
    }

    pub fn run(&self) -> JoinHandle<()> {
        let chain = self.clone();

        tokio::spawn(async move {
            chain.init().await;

            loop {
                chain.begin_block().await;

                tokio::time::sleep(Duration::from_millis(200)).await;

                chain.commit().await;
            }
        })
    }
}
