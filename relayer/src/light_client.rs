use ibc::ics02_client::client_state::AnyClientState;
use ibc::ics02_client::misbehaviour::MisbehaviourEvidence;

use crate::chain::Chain;
use crate::error;
use ibc::ics02_client::events::UpdateClient;

pub mod tendermint;

#[cfg(test)]
pub mod mock;

/// Defines a light block from the point of view of the relayer.
pub trait LightBlock<C: Chain>: Send + Sync {
    fn signed_header(&self) -> &C::Header;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedBlock<LB> {
    /// Verified target block
    pub target: LB,
    /// Supporting headers needed to verify `target`
    pub supporting: Vec<LB>,
}

/// Defines a client from the point of view of the relayer.
pub trait LightClient<C: Chain>: Send + Sync {
    /// Fetch a header from the chain at the given height and verify it
    fn verify(
        &mut self,
        trusted: ibc::Height,
        target: ibc::Height,
        client_state: &AnyClientState,
    ) -> Result<VerifiedBlock<C::LightBlock>, error::Error>;

    /// Given a client update event that includes the header used in a client update,
    /// look for misbehaviour by fetching a header at same or latest height.
    fn check_misbehaviour(
        &mut self,
        update: UpdateClient,
        client_state: &AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, error::Error>;

    /// Fetch a header from the chain at the given height, without verifying it
    fn fetch(&mut self, height: ibc::Height) -> Result<C::LightBlock, error::Error>;
}
