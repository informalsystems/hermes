use std::time::Duration;

use tendermint::lite::types::{Commit as _, Header as _, Requester, ValidatorSet as _};
use tendermint::lite::{SignedHeader, TrustThresholdFraction, TrustedState};

use crate::chain;
use crate::error;
use crate::store;

pub mod trust_options;
pub use trust_options::TrustOptions;

pub struct Client<Chain, Store>
where
    Chain: chain::Chain,
    Store: store::Store<Chain>,
{
    chain: Chain,
    trusted_store: Store,
    trusting_period: Duration,
    trust_threshold: TrustThresholdFraction,

    // FIXME: Use a custom type, because TrustedState requires
    // header at height H and validator set at height H + 1
    last_trusted_state: Option<TrustedState<Chain::Commit, Chain::Header>>,
}

impl<Chain, Store> Client<Chain, Store>
where
    Chain: chain::Chain,
    Store: store::Store<Chain>,
{
    pub async fn new(
        chain: Chain,
        trusted_store: Store,
        trust_options: TrustOptions,
    ) -> Result<Self, error::Error> {
        let mut client = Self::new_from_trusted_store(chain, trusted_store, &trust_options)?;

        if let Some(ref trusted_state) = client.last_trusted_state {
            client
                .check_trusted_header(trusted_state.last_header(), &trust_options)
                .await?;

            if trusted_state.last_header().header().height() < trust_options.height {
                client.init_with_trust_options(trust_options).await?;
            }
        } else {
            client.init_with_trust_options(trust_options).await?;
        }

        Ok(client)
    }

    fn new_from_trusted_store(
        chain: Chain,
        trusted_store: Store,
        trust_options: &TrustOptions,
    ) -> Result<Self, error::Error> {
        let mut client = Self {
            chain,
            trusted_store,
            trusting_period: trust_options.trusting_period,
            trust_threshold: trust_options.trust_threshold.clone(),
            last_trusted_state: None,
        };

        client.restore_trusted_state()?;

        Ok(client)
    }

    fn restore_trusted_state(&mut self) -> Result<(), error::Error> {
        if let Some(last_height) = self.trusted_store.last_height() {
            let last_trusted_state = self
                .trusted_store
                .get(store::StoreHeight::GivenHeight(last_height))?;

            self.last_trusted_state = Some(last_trusted_state.clone());
        }

        Ok(())
    }

    async fn check_trusted_header(
        &self,
        _trusted_header: &SignedHeader<Chain::Commit, Chain::Header>,
        _trust_options: &TrustOptions,
    ) -> Result<(), error::Error> {
        todo!()
    }

    async fn init_with_trust_options(
        &mut self,
        trust_options: TrustOptions,
    ) -> Result<(), error::Error> {
        // TODO: Fetch from primary
        let signed_header = self
            .chain
            .requester()
            .signed_header(trust_options.height)
            .await
            .map_err(|e| error::Kind::Rpc.context(e))?;

        // TODO: Validate basic

        if signed_header.header().hash() != trust_options.hash {
            // TODO: Fail
        }

        // TODO: Compare header with witnesses

        // TODO: Fetch from primary
        let validator_set = self
            .chain
            .requester()
            .validator_set(trust_options.height)
            .await
            .map_err(|e| error::Kind::Rpc.context(e))?;

        if validator_set.hash() != signed_header.header().validators_hash() {
            // TODO: Fail
        }

        // FIXME: Is this necessary?
        signed_header
            .commit()
            .validate(&validator_set)
            .map_err(|e| error::Kind::LightClient.context(e))?;

        // TODO: Uncomment when function is made public
        // tendermint::lite::verifier::verify_commit_trusting(
        //     &validator_set,
        //     signed_header.commit(),
        //     trust_options.trust_threshold
        // )?;

        let trusted_state = TrustedState::new(&signed_header, &validator_set);
        self.update_trusted_state(trusted_state)?;

        Ok(())
    }

    fn update_trusted_state(
        &mut self,
        state: TrustedState<Chain::Commit, Chain::Header>,
    ) -> Result<(), error::Error> {
        if state.last_header().header().validators_hash() != state.validators().hash() {
            // TODO: Fail
        }

        self.trusted_store.add(state.clone())?;

        // TODO: Pruning

        self.last_trusted_state = Some(state);

        Ok(())
    }
}
