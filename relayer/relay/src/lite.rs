use std::marker::PhantomData;

use tendermint::lite::types::{Header, Requester};
use tendermint::lite::{TrustThreshold, TrustedState};

use crate::chain::Chain;
use crate::error;
use crate::store::Store;

pub mod trust_options;
use trust_options::TrustOptions;

pub mod state {
    trait State {}
    trait Trusted: State {}

    pub struct Uninit;
    impl State for Uninit {}

    pub struct InitUntrusted;
    impl State for InitUntrusted {}

    pub struct InitTrusted;
    impl State for InitTrusted {}
    impl Trusted for InitTrusted {}
}

pub struct LiteClient<'a, Chain, Store, State> {
    chain: &'a Chain,
    store: &'a mut Store,
    marker: PhantomData<State>,
}

impl<'a, C, S, S0> LiteClient<'a, C, S, S0> {
    #[inline(always)]
    fn to<S1>(self) -> LiteClient<'a, C, S, S1> {
        LiteClient {
            chain: self.chain,
            store: self.store,
            marker: PhantomData,
        }
    }
}

impl<'a, C, S> LiteClient<'a, C, S, state::Uninit>
where
    C: Chain,
    S: Store<C>,
{
    pub fn new(chain: &'a C, store: &'a mut S) -> Self {
        Self {
            chain,
            store,
            marker: PhantomData,
        }
    }

    pub fn init_without_trust(
        self,
    ) -> Result<LiteClient<'a, C, S, state::InitUntrusted>, error::Error> {
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

        let trusted_state = TrustedState::new(&latest_signed_header, &next_validator_set);

        self.store
            .add(trusted_state)
            .map_err(|e| error::Kind::LiteClient.context(e))?;

        Ok(self.to())
    }

    pub fn init_with_trust(
        self,
        _trust_options: TrustOptions<impl TrustThreshold>,
    ) -> Result<LiteClient<'a, C, S, state::InitTrusted>, error::Error> {
        todo!()
    }
}
