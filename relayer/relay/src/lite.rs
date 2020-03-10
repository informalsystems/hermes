use core::marker::PhantomData;
use tendermint::lite::types::{Header, Requester};
use tendermint_lite::store::{MemStore, State};

use relayer_modules::Height;

use crate::chain::tendermint::TendermintChain;
use crate::chain::Chain;
use crate::error;

trait StoreExt {
    fn has(&self, height: Height) -> bool;
}

impl StoreExt for MemStore {
    fn has(&self, height: Height) -> bool {
        self.get(height).is_ok()
    }
}

pub mod state {
    pub struct Uninit;
    pub struct Init;
}

pub struct LiteClient<'a, C, S> {
    chain: &'a C,
    store: &'a mut MemStore,
    marker: PhantomData<S>,
}

impl<'a, C, S0> LiteClient<'a, C, S0> {
    #[inline(always)]
    fn to<S>(self) -> LiteClient<'a, C, S> {
        LiteClient {
            chain: self.chain,
            store: self.store,
            marker: PhantomData,
        }
    }
}

impl<'a, C> LiteClient<'a, C, state::Uninit>
where
    C: Chain,
{
    pub fn new(chain: &'a C, store: &'a mut MemStore) -> Self {
        Self {
            chain,
            store,
            marker: PhantomData,
        }
    }
}

impl<'a> LiteClient<'a, TendermintChain, state::Uninit> {
    // TODO: Use generic MemStore and move up into generic LiteClient impl
    pub fn init_without_trust(
        self,
    ) -> Result<LiteClient<'a, TendermintChain, state::Init>, error::Error> {
        let req = &self.chain.requester();

        let latest_signed_header = req
            .signed_header(0)
            .map_err(|e| error::Kind::LiteClient.context(e))?;

        let last_trusted_height = latest_signed_header.header().height();

        if self.store.has(last_trusted_height) {
            return Ok(self.to());
        }

        let _validator_set = req
            .validator_set(last_trusted_height)
            .map_err(|e| error::Kind::LiteClient.context(e))?;

        let next_validator_set = req
            .validator_set(last_trusted_height + 1)
            .map_err(|e| error::Kind::LiteClient.context(e))?;

        // TODO: Make `validate` public in tendermint-rs crate
        // tendermint::lite::verifier::validate(
        //     &latest_signed_header,
        //     &validator_set,
        //     &next_validator_set,
        // )
        // .map_err(|e| error::Kind::LiteClient.context(e))?;

        let trusted_state = State::new(&latest_signed_header, &next_validator_set);

        self.store
            .add(trusted_state)
            .map_err(|e| error::Kind::LiteClient.context(e))?;

        Ok(self.to())
    }
}
