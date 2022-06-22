use crate::prelude::*;

use core::any::Any as AnyTrait;
use core::marker::{Send, Sync};

use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error::Error;
use crate::ics23_commitment::commitment::CommitmentRoot;

pub trait ConsensusState: core::fmt::Debug + Send + Sync + AsAny {
    /// Type of client associated with this consensus state (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// Commitment root of the consensus state, which is used for key-value pair verification.
    fn root(&self) -> &CommitmentRoot;

    fn encode_vec(&self) -> Result<Vec<u8>, Error>;
}

pub trait AsAny: AnyTrait {
    fn as_any(&self) -> &dyn AnyTrait;
}

impl<M: AnyTrait + ConsensusState> AsAny for M {
    fn as_any(&self) -> &dyn AnyTrait {
        self
    }
}
