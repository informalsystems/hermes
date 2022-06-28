use crate::prelude::*;

use core::fmt::Debug;

use dyn_clone::DynClone;
use ibc_proto::google::protobuf::Any as ProtoAny;

use crate::core::ics02_client::client_type::ClientType;
use crate::dynamic_typing::AsAny;
use crate::timestamp::Timestamp;
use crate::Height;

/// Abstract of consensus state update information
pub trait Header: Debug + Send + Sync + AsAny + DynClone {
    /// The type of client (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// The height of the consensus state
    fn height(&self) -> Height;

    /// The timestamp of the consensus state
    fn timestamp(&self) -> Timestamp;

    /// Encode to canonical protobuf representation
    fn encode_any(&self) -> ProtoAny;

    /// Consumes the given instance and returns a heap allocated instance
    fn boxed(self) -> Box<dyn Header>
    where
        Self: Sized,
    {
        Box::new(self)
    }
}

dyn_clone::clone_trait_object!(Header);
