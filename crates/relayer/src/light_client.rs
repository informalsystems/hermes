pub mod io;
pub mod tendermint;

use ibc_relayer_types::{
    core::ics02_client::events::UpdateClient,
    Height,
};

use crate::{
    chain::endpoint::ChainEndpoint,
    client_state::AnyClientState,
    error,
    misbehaviour::MisbehaviourEvidence,
};

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
        trusted: Height,
        target: Height,
        client_state: &AnyClientState,
        now: C::Time,
    ) -> Result<Verified<C::Header>, error::Error>;

    /// Fetch a header from the chain at the given height and verify it.
    fn verify(
        &mut self,
        trusted: Height,
        target: Height,
        client_state: &AnyClientState,
        now: C::Time,
    ) -> Result<Verified<C::LightBlock>, error::Error>;

    /// Given a client update event that includes the header used in a client update,
    /// run the light client attack detector.
    fn detect_misbehaviour(
        &mut self,
        update: &UpdateClient,
        client_state: &AnyClientState,
        now: C::Time,
    ) -> Result<Option<MisbehaviourEvidence>, error::Error>;

    /// Fetch a header from the chain at the given height, without verifying it
    fn fetch(&mut self, height: Height) -> Result<C::LightBlock, error::Error>;
}
