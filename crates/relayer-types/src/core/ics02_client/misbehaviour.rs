use core::fmt::Debug;

use crate::{
    core::ics24_host::identifier::ClientId,
    Height,
};

pub trait Misbehaviour: Clone + Debug + Send + Sync {
    /// The type of client (eg. Tendermint)
    fn client_id(&self) -> &ClientId;

    /// The height of the consensus state
    fn height(&self) -> Height;
}
