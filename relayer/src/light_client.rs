use crate::chain::Chain;
use crate::error;

pub mod tendermint;

#[cfg(test)]
pub mod mock;

/// Defines a light block from the point of view of the relayer.
pub trait LightBlock<C: Chain>: Send + Sync {
    fn signed_header(&self) -> &C::Header;
}

/// Defines a client from the point of view of the relayer.
pub trait LightClient<C: Chain>: Send + Sync {
    /// Fetch and verify the latest header from the chain
    fn verify_to_latest(&mut self, trusted: ibc::Height) -> Result<C::LightBlock, error::Error>;

    /// Fetch and verify the header from the chain at the given height
    fn verify_to_target(
        &mut self,
        trusted: ibc::Height,
        target: ibc::Height,
    ) -> Result<C::LightBlock, error::Error>;
}
