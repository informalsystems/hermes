use std::fmt::Debug;
use std::sync::Arc;
use std::sync::Mutex;

use basecoin_app::modules::auth::Auth;
use basecoin_app::modules::bank::Bank;
use basecoin_app::modules::context::prefix;
use basecoin_app::modules::context::Identifiable;
use basecoin_app::modules::ibc::Ibc;
use basecoin_app::BaseCoinApp;
use basecoin_app::Builder;
use basecoin_store::context::ProvableStore;
use ibc::core::ics24_host::identifier::ChainId;
use tendermint_testgen::light_block::TmLightBlock;
use tokio::task::JoinHandle;

use crate::traits::handle::BasecoinHandle;

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

    pub fn start(&self) -> JoinHandle<()> {
        let chain = self.clone();

        tokio::spawn(async move {
            chain.run().await;
        })
    }
}
