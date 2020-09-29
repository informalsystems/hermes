use crate::ics02_client::client_def::AnyClientState;
use crate::ics24_host::identifier::ClientId;
use crate::Height;

/// Trait capturing all dependencies (i.e., the context) which algorithms in ICS18 require to
/// relay packets between chains. This trait comprises the dependencies towards a single chain.
/// TODO -- eventually this trait should mirror the `Chain` trait.
pub trait ICS18Context {
    /// Returns the latest height of the chain.
    fn query_latest_height(&self) -> Height;

    /// MockClientState->latest_height() of this client
    fn query_client_full_state(&self, client_id: &ClientId) -> Option<AnyClientState>;
}
