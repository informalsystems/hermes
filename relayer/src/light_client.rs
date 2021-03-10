use crate::chain::Chain;
use crate::error;
use ibc::ics02_client::client_misbehaviour::AnyMisbehaviour;
use ibc::ics02_client::events::UpdateClient;

pub mod tendermint;

#[cfg(test)]
pub mod mock;

/// Defines a light block from the point of view of the relayer.
pub trait LightBlock<C: Chain>: Send + Sync {
    fn signed_header(&self) -> &C::Header;
}

/// Defines a client from the point of view of the relayer.
pub trait LightClient<C: Chain>: Send + Sync {
    /// Get the latest trusted state of the light client
    fn latest_trusted(&self) -> Result<Option<C::LightBlock>, error::Error>;

    /// Fetch and verify the latest header from the chain
    fn verify_to_latest(&self) -> Result<C::LightBlock, error::Error>;

    /// Fetch and verify the header from the chain at the given height
    fn verify_to_target(&self, height: ibc::Height) -> Result<C::LightBlock, error::Error>;

    /// Compute the minimal ordered set of heights needed to update the light
    /// client state from from `latest_client_state_height` to `target_height`.
    fn get_minimal_set(
        &self,
        latest_client_state_height: ibc::Height,
        target_height: ibc::Height,
    ) -> Result<Vec<ibc::Height>, error::Error>;

    fn build_misbehaviour(
        &self,
        update: UpdateClient,
        trusted_height: ibc::Height,
        latest_chain_height: ibc::Height,
    ) -> Result<Option<AnyMisbehaviour>, error::Error>;
}
