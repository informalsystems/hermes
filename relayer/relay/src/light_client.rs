use std::marker::PhantomData;
use std::time::Duration;

use tendermint::lite::types::{Header, Requester};
use tendermint::lite::{TrustThreshold, TrustThresholdFraction, TrustedState};

use crate::chain::{query_header_at_height, query_latest_height, Chain};
use crate::error;
use crate::store::{Store, StoreHeight};

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

pub struct LightClient<'a, Chain, Store, State> {
    chain: &'a Chain,
    store: &'a mut Store,
    marker: PhantomData<State>,
}

impl<'a, C, S, S0> LightClient<'a, C, S, S0> {
    #[inline(always)]
    fn to<S1>(self) -> LightClient<'a, C, S, S1> {
        LightClient {
            chain: self.chain,
            store: self.store,
            marker: PhantomData,
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
            marker: PhantomData,
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
            return Ok(self.to());
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

        Ok(self.to())
    }

    pub async fn init_with_node_trusted_state(
        self,
    ) -> Result<LightClient<'a, C, S, state::InitTrusted>, error::Error>
    where
        C: Chain,
    {
        let height = query_latest_height(self.chain).await?;
        let header = query_header_at_height(self.chain, height).await?;
        let period = Duration::from_secs(2);
        let trust_threshold = TrustThresholdFraction::default();

        let trust_options =
            TrustOptions::new(period, height, header.header().hash(), trust_threshold)?;

        self.init_with_trusted_state(trust_options)
    }

    pub fn init_with_trusted_state(
        self,
        _trust_options: TrustOptions<impl TrustThreshold>,
    ) -> Result<LightClient<'a, C, S, state::InitTrusted>, error::Error> {
        todo!()
    }
}
