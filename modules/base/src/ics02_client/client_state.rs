use core::marker::{Send, Sync};

use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error::Error;
use crate::ics24_host::identifier::ChainId;
use crate::prelude::*;
use crate::Height;

pub trait ClientState: core::fmt::Debug + Send + Sync {
    /// Client-specific options for upgrading the client
    type UpgradeOptions;

    /// Return the chain identifier which this client is serving (i.e., the client is verifying
    /// consensus states from this chain).
    fn chain_id(&self) -> ChainId;

    /// Type of client associated with this state (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// Latest height of consensus state
    fn latest_height(&self) -> Height;

    /// Freeze status of the client
    fn is_frozen(&self) -> bool {
        self.frozen_height().is_some()
    }

    /// Frozen height of the client
    fn frozen_height(&self) -> Option<Height>;

    /// Helper function to verify the upgrade client procedure.
    /// Resets all fields except the blockchain-specific ones,
    /// and updates the given fields.
    fn upgrade(
        &mut self,
        upgrade_height: Height,
        upgrade_options: Self::UpgradeOptions,
        chain_id: ChainId,
    );

    fn encode_vec(&self) -> Result<Vec<u8>, Error>;
}
