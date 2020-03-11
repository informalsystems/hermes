#![allow(dead_code)]

use tendermint::lite::types::{Header, Requester};
use tendermint::lite::TrustedState;

use crate::chain::{query_header_at_height, query_latest_height, Chain};
use crate::error;
use crate::store::{Store, StoreHeight};

pub mod trust_options;
use trust_options::TrustOptions;

pub mod state {
    use super::*;

    trait State {}
    trait Trusted: State {}

    pub struct Uninit;
    impl State for Uninit {}

    pub struct InitUntrusted;
    impl State for InitUntrusted {}

    pub struct InitTrusted {
        trust_options: TrustOptions,
    }

    impl State for InitTrusted {}
    impl Trusted for InitTrusted {}
    impl InitTrusted {
        pub fn new(trust_options: TrustOptions) -> Self {
            Self { trust_options }
        }
    }
}

pub struct LightClient<'a, Chain, Store, State> {
    chain: &'a Chain,
    store: &'a mut Store,
    state: State,
}

impl<'a, C, S, S0> LightClient<'a, C, S, S0> {
    #[inline(always)]
    fn to<S1>(self, state: S1) -> LightClient<'a, C, S, S1> {
        LightClient {
            chain: self.chain,
            store: self.store,
            state,
        }
    }
}

impl<'a, C, S> LightClient<'a, C, S, state::Uninit>
where
    C: Chain,
    S: Store<C>,
{
    pub fn new(chain: &'a C, store: &'a mut S) -> Self {
        Self {
            chain,
            store,
            state: state::Uninit,
        }
    }

    pub async fn init_without_trusted_state(
        self,
    ) -> Result<LightClient<'a, C, S, state::InitUntrusted>, error::Error> {
        let req = &self.chain.requester();

        let latest_signed_header = req
            .signed_header(0)
            .await
            .map_err(|e| error::Kind::LightClient.context(e))?;

        let last_trusted_height = latest_signed_header.header().height();

        let store_height = StoreHeight::GivenHeight(last_trusted_height);

        if self.store.has(store_height) {
            return Ok(self.to(state::InitUntrusted));
        }

        let _validator_set = req
            .validator_set(last_trusted_height)
            .await
            .map_err(|e| error::Kind::LightClient.context(e))?;

        let next_validator_set = req
            .validator_set(last_trusted_height + 1)
            .await
            .map_err(|e| error::Kind::LightClient.context(e))?;

        // TODO: Make `validate` public in tendermint-rs crate
        // tendermint::lite::verifier::validate(
        //     &latest_signed_header,
        //     &validator_set,
        //     &next_validator_set,
        // )
        // .map_err(|e| error::Kind::LightClient.context(e))?;

        let trusted_state = TrustedState::new(&latest_signed_header, &next_validator_set);

        self.store
            .add(trusted_state)
            .map_err(|e| error::Kind::LightClient.context(e))?;

        Ok(self.to(state::InitUntrusted))
    }

    pub async fn init_with_node_trusted_state(
        self,
    ) -> Result<LightClient<'a, C, S, state::InitTrusted>, error::Error>
    where
        C: Chain,
    {
        let height = query_latest_height(self.chain).await?;
        let header = query_header_at_height(self.chain, height).await?;

        let trusting_period = self.chain.trusting_period();
        let trust_threshold = self.chain.trust_threshold();

        let trust_options = TrustOptions::new(
            trusting_period,
            height,
            header.header().hash(),
            trust_threshold,
        )?;

        self.init_with_trust(trust_options)
    }

    pub fn init_with_trust(
        self,
        trust_options: TrustOptions,
    ) -> Result<LightClient<'a, C, S, state::InitTrusted>, error::Error> {
        Ok(self.to(state::InitTrusted::new(trust_options)))
    }
}
