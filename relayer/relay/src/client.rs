use std::cmp::Ordering;
use std::time::{Duration, SystemTime};

use anomaly::fail;

use tendermint::lite::types::{Commit, Header as _, Requester, ValidatorSet as _};
use tendermint::lite::{SignedHeader, TrustThresholdFraction, TrustedState};

use crate::chain;
use crate::error;
use crate::store::{self, StoreHeight};

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

    // FIXME: Use a custom type, because TrustedState states
    // it holds a header at height H and validator set at height H + 1,
    // whereas this trusted state holds both header and validator set at
    // same height H
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

        let _ = client.update(SystemTime::now()).await?;

        Ok(client)
    }

    pub fn last_trusted_state(&self) -> Option<&TrustedState<Chain::Commit, Chain::Header>> {
        self.last_trusted_state.as_ref()
    }

    pub async fn update(
        &mut self,
        now: SystemTime,
    ) -> Result<Option<SignedHeader<Chain::Commit, Chain::Header>>, error::Error> {
        match self.last_trusted_state {
            Some(ref last_trusted_state) => {
                let last_trusted_height = last_trusted_state.last_header().header().height();

                let latest_header = self
                    .chain
                    .requester()
                    .signed_header(0)
                    .await
                    .map_err(|e| error::Kind::LightClient.context(e))?;

                let latest_validator_set = self
                    .chain
                    .requester()
                    .validator_set(latest_header.header().height())
                    .await
                    .map_err(|e| error::Kind::LightClient.context(e))?;

                if latest_header.header().height() > last_trusted_height {
                    self.verify_header(&latest_header, &latest_validator_set, now)
                        .await?;

                    Ok(Some(latest_header))
                } else {
                    Ok(None)
                }
            }
            None => fail!(error::Kind::LightClient, "can't get last trusted state"),
        }
    }

    // TODO: Cleanup signature
    async fn verify_header(
        &mut self,
        new_header: &SignedHeader<Chain::Commit, Chain::Header>,
        new_validator_set: &<<Chain as chain::Chain>::Commit as Commit>::ValidatorSet,
        now: SystemTime,
    ) -> Result<(), error::Error> {
        let in_store = self
            .trusted_store
            .get(StoreHeight::Given(new_header.header().height()));

        if let Ok(state) = in_store {
            let stored_header = state.last_header().header();
            if stored_header.hash() != new_header.header().hash() {
                fail!(
                    error::Kind::LightClient,
                    "existing trusted header {} does not match new header {}",
                    stored_header.hash(),
                    new_header.header().hash()
                )
            }
        }

        if let Some(ref last_trusted_state) = self.last_trusted_state {
            let next_height = new_header
                .header()
                .height()
                .checked_add(1)
                .expect("height overflow");

            let new_next_validator_set = self
                .chain
                .requester()
                .validator_set(next_height)
                .await
                .map_err(|e| error::Kind::LightClient.context(e))?;

            tendermint::lite::verifier::verify_single(
                last_trusted_state.clone(),
                &new_header,
                &new_validator_set,
                &new_next_validator_set,
                self.trust_threshold,
                self.trusting_period,
                now,
            )
            .map_err(|e| error::Kind::LightClient.context(e))?;

            // TODO: Compare new header with witnesses (?)

            let new_trusted_state =
                TrustedState::new(new_header.clone(), new_validator_set.clone());

            self.update_trusted_state(new_trusted_state)?;

            Ok(())
        } else {
            fail!(
                error::Kind::LightClient,
                "no current trusted state to verify new header with"
            )
        }
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
            trust_threshold: trust_options.trust_threshold,
            last_trusted_state: None,
        };

        client.restore_trusted_state()?;

        Ok(client)
    }

    fn restore_trusted_state(&mut self) -> Result<(), error::Error> {
        if let Some(last_height) = self.trusted_store.last_height() {
            let last_trusted_state = self
                .trusted_store
                .get(store::StoreHeight::Given(last_height))?;

            self.last_trusted_state = Some(last_trusted_state.clone());
        }

        Ok(())
    }

    async fn check_trusted_header(
        &self,
        trusted_header: &SignedHeader<Chain::Commit, Chain::Header>,
        trust_options: &TrustOptions,
    ) -> Result<(), error::Error> {
        let primary_hash = match trust_options.height.cmp(&trusted_header.header().height()) {
            Ordering::Greater => {
                // TODO: Fetch from primary (?)
                self.chain
                    .requester()
                    .signed_header(trust_options.height)
                    .await
                    .map_err(|e| error::Kind::Rpc.context(e))?
                    .header()
                    .hash()
            }
            Ordering::Equal => trust_options.hash,
            Ordering::Less => {
                // TODO: Implement rollback
                trust_options.hash
            }
        };

        if primary_hash != trusted_header.header().hash() {
            // TODO: Implement cleanup
        }

        Ok(())
    }

    async fn init_with_trust_options(
        &mut self,
        trust_options: TrustOptions,
    ) -> Result<(), error::Error> {
        // TODO: Fetch from primary (?)
        let signed_header = self
            .chain
            .requester()
            .signed_header(trust_options.height)
            .await
            .map_err(|e| error::Kind::Rpc.context(e))?;

        // TODO: Validate basic

        if trust_options.hash != signed_header.header().hash() {
            fail!(
                error::Kind::LightClient,
                "expected header's hash {}, but got {}",
                trust_options.hash,
                signed_header.header().hash()
            )
        }

        // TODO: Compare header with witnesses (?)

        // TODO: Fetch from primary (?)
        let validator_set = self
            .chain
            .requester()
            .validator_set(trust_options.height)
            .await
            .map_err(|e| error::Kind::Rpc.context(e))?;

        if signed_header.header().validators_hash() != validator_set.hash() {
            fail!(
                error::Kind::LightClient,
                "expected header's validators ({}) to match those that were supplied ({})",
                signed_header.header().validators_hash(),
                validator_set.hash()
            )
        }

        // FIXME: Is this necessary?
        signed_header
            .commit()
            .validate(&validator_set)
            .map_err(|e| error::Kind::LightClient.context(e))?;

        tendermint::lite::verifier::verify_commit_trusting(
            &validator_set,
            signed_header.commit(),
            trust_options.trust_threshold,
        )
        .map_err(|e| error::Kind::LightClient.context(e))?;

        let trusted_state = TrustedState::new(signed_header, validator_set);
        self.update_trusted_state(trusted_state)?;

        Ok(())
    }

    fn update_trusted_state(
        &mut self,
        state: TrustedState<Chain::Commit, Chain::Header>,
    ) -> Result<(), error::Error> {
        if state.last_header().header().validators_hash() != state.validators().hash() {
            fail!(
                error::Kind::LightClient,
                "expected validator's hash {}, but got {}",
                state.last_header().header().validators_hash(),
                state.validators().hash()
            )
        }

        self.trusted_store.add(state.clone())?;

        // TODO: Pruning

        self.last_trusted_state = Some(state);

        Ok(())
    }
}
