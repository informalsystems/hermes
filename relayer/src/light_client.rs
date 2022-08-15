use ibc::core::ics02_client::client_state::AnyClientState;
use ibc::core::ics02_client::misbehaviour::MisbehaviourEvidence;

use crate::chain::endpoint::ChainEndpoint;
use crate::error;
use ibc::core::ics02_client::events::UpdateClient;

pub mod tendermint;

#[cfg(test)]
pub mod mock;

/// Defines a light block from the point of view of the relayer.
pub trait LightBlock<C: ChainEndpoint>: Send + Sync {
    fn signed_header(&self) -> &C::Header;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Verified<H> {
    /// Verified target
    pub target: H,
    /// Supporting headers needed to verify `target`
    pub supporting: Vec<H>,
}

/// Defines a client from the point of view of the relayer.
pub trait LightClient<C: ChainEndpoint>: Send + Sync {
    /// Fetch and verify a header, and return its minimal supporting set.
    fn header_and_minimal_set(
        &mut self,
        trusted: ibc::Height,
        target: ibc::Height,
        client_state: &AnyClientState,
    ) -> Result<Verified<C::Header>, error::Error>;

    /// Fetch a header from the chain at the given height and verify it.
    fn verify(
        &mut self,
        trusted: ibc::Height,
        target: ibc::Height,
        client_state: &AnyClientState,
    ) -> Result<Verified<C::LightBlock>, error::Error>;

    /// Given a client update event that includes the header used in a client update,
    /// look for misbehaviour by fetching a header at same or latest height.
    fn check_misbehaviour(
        &mut self,
        update: &UpdateClient,
        client_state: &AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, error::Error>;

    /// Fetch a header from the chain at the given height, without verifying it
    fn fetch(&mut self, height: ibc::Height) -> Result<C::LightBlock, error::Error>;
}
