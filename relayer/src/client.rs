use std::cmp::Ordering;
use std::time::{Duration, SystemTime};

use anomaly::fail;
use tracing::{debug, info, warn};

use ibc::Height;

use tendermint_light_client::supervisor::Handle;
use tendermint_light_client::types::{LightBlock, TrustThreshold};

use crate::chain;
use crate::error;
use crate::store::{self, StoreHeight};

pub mod trust_options;
pub use trust_options::TrustOptions;

/// Defines a client from the point of view of the relayer.
///
/// This is basically a wrapper around the facilities provided
/// by the light client implementation in the `tendermint-rs` crate,
/// where verified headers are stored in a trusted store.
pub struct Client<Chain, Store>
where
    Chain: chain::Chain,
    Store: store::Store<Chain>,
{
    /// The chain this client is for
    chain: Chain,

    /// The trusted store where to store the trust options, TODO: Rename
    trusted_store: Store,

    /// The trusting period configured for this chain
    trusting_period: Duration,

    /// The trust threshold configured for this chain
    trust_threshold: TrustThreshold,

    /// The last trusted state verified by this client
    last_trusted_state: Option<Chain::LightBlock>,
}

//impl<Chain, Store> Client<Chain, Store>
//where
//    Chain: chain::Chain,
//    Store: store::Store<Chain>,
//{
//    /// Create a new `Client` for the given `Chain` with the given trusted store
//    /// and trust options, and try to restore the last trusted state from the trusted store.
//    pub fn new_from_trusted_store(
//        chain: Chain,
//        trusted_store: Store,
//        trust_options: &TrustOptions,
//    ) -> Result<Self, error::Error> {
//        debug!(
//            chain.id = %chain.id(),
//            "initializing client from trusted store",
//        );

//        let mut client = Self {
//            chain,
//            trusted_store,
//            trusting_period: trust_options.trusting_period,
//            trust_threshold: trust_options.trust_threshold,
//            last_trusted_state: None,
//        };

//        client.restore_trusted_state()?;

//        Ok(client)
//    }

//    /// Create a new `Client` for the given `chain`, storing headers
//    /// in the given `trusted_store`, and verifying them with the
//    /// given `trust_options`.
//    ///
//    /// This method is async because it needs to pull the latest header
//    /// from the chain, verify it, and store it.
//    pub async fn new_from_trust_options(
//        chain: Chain,
//        trusted_store: Store,
//        trust_options: &TrustOptions,
//    ) -> Result<Self, error::Error> {
//        let mut client = Self::new_from_trusted_store(chain, trusted_store, &trust_options)?;

//        // If we already have a last trusted state
//        if let Some(ref trusted_state) = client.last_trusted_state {
//            debug!("found last trusted state");

//            // Check that the last trusted header can actually be trusted with the given trust options
//            // client
//            //     .check_trusted_header(trusted_state.last_header(), &trust_options)
//            //     .await?;

//            debug!("trusted header was valid");

//            // If the last header we trust is below the given trusted height, we need
//            // to fetch and verify the header at the given trusted height instead.
//            let last_header_height: Height = todo!(); // trusted_state.last_header().header().height();

//            if last_header_height < trust_options.height {
//                // debug!(
//                //     last_header.height = last_header_height,
//                //     trust_options.height, "last header height below trust options height"
//                // );

//                client.init_with_trust_options(trust_options).await?;
//            }
//        } else {
//            // Otherwise, init the client with the given trusted height, etc.
//            client.init_with_trust_options(trust_options).await?;
//        }

//        Ok(client)
//    }

//    /// The last state (if any) trusted by this client
//    pub fn last_trusted_state(&self) -> Option<&LightBlock> {
//        self.last_trusted_state.as_ref()
//    }

//    /// The chain for which this client is configured
//    pub fn chain(&self) -> &Chain {
//        &self.chain
//    }

//    /// Fetch and verify the latest header from the chain
//    ///
//    /// If the fetched header is higher than the previous trusted state,
//    /// and it verifies then we succeed and return it wrapped in `Some(_)`.
//    ///
//    /// If it is higher but does not verify we fail with an error.
//    ///
//    /// If it is lower we succeed but return `None`.
//    ///
//    /// If there is no trusted state yet we fail with an error.
//    pub async fn update(&mut self, now: SystemTime) -> Result<Option<LightBlock>, error::Error> {
//        match self.last_trusted_state {
//            Some(ref last_trusted_state) => {
//                let last_trusted_height = last_trusted_state.last_header().header().height();

//                let latest_header = self
//                    .chain
//                    .requester()
//                    .signed_header(0)
//                    .await
//                    .map_err(|e| error::Kind::LightClient.context(e))?;

//                if latest_header.header().height() > last_trusted_height {
//                    self.verify_header(&latest_header, now).await?;

//                    Ok(Some(latest_header))
//                } else {
//                    Ok(None)
//                }
//            }
//            None => fail!(error::Kind::LightClient, "can't get last trusted state"),
//        }
//    }

//    /// Verify the given signed header and validator set against the
//    /// trusted store.
//    ///
//    /// If the given header is already in the store, but it does not match
//    /// the stored hash, we fail with an error.
//    ///
//    /// Otherwise, and only if we already have a trusted state,
//    /// we attempt bisection for the new header at the given height.
//    /// If this succeeds, we add the new trusted states to the store and
//    /// update our last trusted state.
//    ///
//    /// In any other case, we fail with an error.
//    async fn verify_header(
//        &mut self,
//        new_header: &Chain::LightBlock,
//        now: SystemTime,
//    ) -> Result<(), error::Error> {
//        let in_store = self
//            .trusted_store
//            .get(StoreHeight::Given(new_header.header().height()));

//        // If the given header height is already in the store
//        if let Ok(state) = in_store {
//            let stored_header = state.last_header().header();

//            // ... but it does not match the stored hash, then we fail
//            if stored_header.hash() != new_header.header().hash() {
//                fail!(
//                    error::Kind::LightClient,
//                    "existing trusted header {} does not match new header {}",
//                    stored_header.hash(),
//                    new_header.header().hash()
//                )
//            }
//        }

//        // If we already have a trusted state, we attempt bisection for the
//        // new header at the given height. If it succeeds, we add the new
//        // trusted states to the store and update our last trusted state.
//        if let Some(ref last_trusted_state) = self.last_trusted_state {
//            let new_header_height = new_header.header().height();

//            let new_trusted_states: Vec<LightBlock> = todo!();
//            // let new_trusted_states = tendermint::lite::verifier::verify_bisection(
//            //     last_trusted_state.clone(),
//            //     new_header_height,
//            //     self.trust_threshold,
//            //     self.trusting_period,
//            //     now,
//            //     self.chain.requester(),
//            // )
//            // .await
//            // .map_err(|e| error::Kind::LightClient.context(e))?;

//            for new_trusted_state in new_trusted_states {
//                self.update_trusted_state(new_trusted_state)?;
//            }

//            Ok(())
//        } else {
//            fail!(
//                error::Kind::LightClient,
//                "no current trusted state to verify new header with"
//            )
//        }
//    }

//    /// Restore the last trusted state from the state, by asking for
//    /// its last stored height, without any verification.
//    fn restore_trusted_state(&mut self) -> Result<(), error::Error> {
//        if let Some(last_height) = self.trusted_store.last_height()? {
//            debug!(
//                chain.id = %self.chain.id(),
//                "restoring trusted state from store",
//            );

//            let last_trusted_state = self
//                .trusted_store
//                .get(store::StoreHeight::Given(last_height))?;

//            debug!(
//                chain.id = %self.chain.id(),
//                last_height = last_height,
//                "found trusted state in store",
//            );

//            self.last_trusted_state = Some(last_trusted_state);
//        } else {
//            debug!(
//                chain.id = %self.chain.id(),
//                "no last height recorded in trusted store",
//            );
//        }

//        Ok(())
//    }

//    /// Check that the given trusted state corresponding to the given
//    /// trust options is valid.
//    ///
//    /// TODO: Improve doc
//    /// TODO: Impement rollback
//    /// TODO: Implement cleanup
//    async fn check_trusted_header(
//        &self,
//        trusted_header: &LightBlock,
//        trust_options: &TrustOptions,
//    ) -> Result<(), error::Error> {
//        debug!(
//            chain.id = %self.chain.id(),
//            "restoring trusted state from store",
//        );

//        let primary_hash = match trust_options.height.cmp(&trusted_header.header().height()) {
//            Ordering::Greater => {
//                debug!(
//                    chain.id = %self.chain.id(),
//                    trust_options.height,
//                    trusted_header.height = trusted_header.header().height(),
//                    "trusted options height is greater than trusted header height",
//                );

//                self.chain
//                    .requester()
//                    .signed_header(trust_options.height)
//                    .await
//                    .map_err(|e| error::Kind::Rpc.context(e))?
//                    .header()
//                    .hash()
//            }
//            Ordering::Equal => {
//                debug!(
//                    chain.id = %self.chain.id(),
//                    trust_options.height,
//                    trusted_header.height = trusted_header.header().height(),
//                    "trusted options height is equal to trusted header height",
//                );

//                trust_options.hash
//            }
//            Ordering::Less => {
//                debug!(
//                    chain.id = %self.chain.id(),
//                    trust_options.height,
//                    trusted_header.height = trusted_header.header().height(),
//                    "trusted options height is lesser than trusted header height",
//                );

//                info!(
//                    chain.id = %self.chain.id(),
//                    old = %trust_options.height,
//                    trusted_header.height = %trusted_header.header().height(),
//                    trusted_header.hash = %trusted_header.header().hash(),
//                    "client initialized with old header (trusted header is more recent)",
//                );

//                // TODO: Rollback: Remove all headers in (trust_options.height, trusted_header.height]

//                trust_options.hash
//            }
//        };

//        debug!(
//            chain.id = %self.chain.id(),
//            primary.hash = %primary_hash,
//            trusted_header.hash = %trusted_header.header().hash(),
//            "comparing trusted_header.hash against primary.hash",
//        );

//        if primary_hash != trusted_header.header().hash() {
//            // TODO: Implement cleanup

//            warn!(
//                chain.id = %self.chain.id(),
//                primary.hash = %primary_hash,
//                trusted_header.hash = %trusted_header.header().hash(),
//                "trusted header hash and primary header hash do not match, rolling back (TODO)",
//            );
//        } else {
//            debug!(
//                chain.id = %self.chain.id(),
//                primary.hash = %primary_hash,
//                trusted_header.hash = %trusted_header.header().hash(),
//                "trusted header hash and primary header hash match",
//            );
//        }

//        Ok(())
//    }

//    /// Initialize this client with the given trust options.
//    ///
//    /// This pulls the header and validator set at the height specified in
//    /// the trust options, and checks their hashes against the hashes
//    /// specified in the trust options.
//    ///
//    /// Then validate the commit against its validator set.
//    ///
//    /// Then verify that +1/3 of the validator set signed the commit.
//    ///
//    /// If everything succeeds, add the header to the trusted store and
//    /// update the last trusted state with it.
//    async fn init_with_trust_options(
//        &mut self,
//        trust_options: &TrustOptions,
//    ) -> Result<(), error::Error> {
//        debug!("initialize client with given trust_options");

//        // TODO: Fetch from primary (?)
//        let signed_header = self
//            .chain
//            .requester()
//            .signed_header(trust_options.height)
//            .await
//            .map_err(|e| error::Kind::Rpc.context(e))?;

//        debug!(
//            trust_options.height,
//            header.hash = %signed_header.header().hash(),
//            "fetched header at height {}", trust_options.height
//        );

//        // TODO: Validate basic

//        if trust_options.hash != signed_header.header().hash() {
//            fail!(
//                error::Kind::LightClient,
//                "expected header's hash {}, but got {}",
//                trust_options.hash,
//                signed_header.header().hash()
//            )
//        }

//        // TODO: Compare header with witnesses (?)

//        debug!("TODO: compare header with witnesses");

//        // TODO: Fetch from primary (?)
//        let validator_set = self
//            .chain
//            .requester()
//            .validator_set(trust_options.height)
//            .await
//            .map_err(|e| error::Kind::Rpc.context(e))?;

//        debug!(
//            trust_options.height,
//            validator_set.hash = %validator_set.hash(),
//            header.validators_hash = %signed_header.header().validators_hash(),
//            "fetched validator set at height {}", trust_options.height);

//        if signed_header.header().validators_hash() != validator_set.hash() {
//            fail!(
//                error::Kind::LightClient,
//                "expected header's validators ({}) to match those that were supplied ({})",
//                signed_header.header().validators_hash(),
//                validator_set.hash()
//            )
//        }

//        debug!("validator set hashes match");

//        // FIXME: Is this necessary?
//        signed_header
//            .commit()
//            .validate(&validator_set)
//            .map_err(|e| error::Kind::LightClient.context(e))?;

//        debug!("header is valid");

//        // tendermint::lite::verifier::verify_commit_trusting(
//        //     &validator_set,
//        //     signed_header.commit(),
//        //     trust_options.trust_threshold,
//        // )
//        // .map_err(|e| error::Kind::LightClient.context(e))?;

//        debug!("verify_commit_trusting result is valid");

//        let trusted_state = todo!();
//        self.update_trusted_state(trusted_state)?;

//        Ok(())
//    }

//    /// Update the last trusted state with the given state,
//    /// and add it to the trusted store.
//    ///
//    /// This method only verifies that the validators hashes match.
//    ///
//    /// TODO: Pruning
//    fn update_trusted_state(&mut self, state: LightBlock) -> Result<(), error::Error> {
//        if state.last_header().header().validators_hash() != state.validators().hash() {
//            fail!(
//                error::Kind::LightClient,
//                "expected validator's hash {}, but got {}",
//                state.last_header().header().validators_hash(),
//                state.validators().hash()
//            )
//        }

//        self.trusted_store.add(state.clone())?;

//        // TODO: Pruning

//        debug!(
//            state.header.hash = %state.last_header().header().hash(),
//            state.header.height = state.last_header().header().height(),
//            "updated trusted store"
//        );

//        self.last_trusted_state = Some(state);

//        Ok(())
//    }
//}
