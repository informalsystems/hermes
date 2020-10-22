use crate::ics02_client::client_def::{AnyClientState, AnyHeader};
use crate::ics18_relayer::error::Error;
use crate::ics24_host::identifier::ClientId;
use crate::ics26_routing::msgs::ICS26Envelope;
use crate::Height;

/// Trait capturing all dependencies (i.e., the context) which algorithms in ICS18 require to
/// relay packets between chains. This trait comprises the dependencies towards a single chain.
/// Most of the functions in this represent wrappers over the ABCI interface.
/// TODO -- eventually this trait should mirror the `Chain` trait.
pub trait ICS18Context {
    /// Returns the latest height of the chain.
    fn query_latest_height(&self) -> Height;

    /// Returns this client state for the given `client_id` on this chain.
    /// Wrapper over the `/abci_query?path=..` endpoint.
    fn query_client_full_state(&self, client_id: &ClientId) -> Option<AnyClientState>;

    /// Returns the most advanced header of this chain.
    fn query_latest_header(&self) -> Option<AnyHeader>;

    /// Interface that the relayer uses to submit a datagram to this chain.
    /// Wraps around the `/broadcast_tx_async` ABCI endpoint.
    fn send(&mut self, msg: ICS26Envelope) -> Result<(), Error>;
}
