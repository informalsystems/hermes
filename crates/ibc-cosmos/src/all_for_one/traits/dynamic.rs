use ibc::core::ics23_commitment::merkle::MerkleProof;
use ibc::core::ics24_host::identifier::ClientId;
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_framework::all_for_one::traits::base::AfoChainContext;
use ibc_framework::core::traits::error::InjectError;
use ibc_framework::core::traits::stores::client_reader::HasClientReader;
use ibc_proto::google::protobuf::Any;

use crate::clients::dynamic::client::{
    DynClientHeader, DynClientState, DynConsensusState, DynMisbehavior,
};
use crate::clients::tendermint::client::TendermintClient;
use crate::clients::tendermint::update_client::Error as UpdateTendermintClientError;

pub trait AfoDynamicChainContext:
    AfoChainContext<
        Height = Height,
        Timestamp = Timestamp,
        Message = Any,
        ClientId = ClientId,
        MerkleProof = MerkleProof,
        AnyClientState = DynClientState,
        AnyConsensusState = DynConsensusState,
        AnyClientHeader = DynClientHeader,
        AnyMisbehavior = DynMisbehavior,
    > + InjectError<UpdateTendermintClientError>
    + HasClientReader<TendermintClient>
{
}

impl<Context> AfoDynamicChainContext for Context where
    Context: AfoChainContext<
            Height = Height,
            Timestamp = Timestamp,
            Message = Any,
            ClientId = ClientId,
            MerkleProof = MerkleProof,
            AnyClientState = DynClientState,
            AnyConsensusState = DynConsensusState,
            AnyClientHeader = DynClientHeader,
            AnyMisbehavior = DynMisbehavior,
        > + InjectError<UpdateTendermintClientError>
        + HasClientReader<TendermintClient>
{
}
