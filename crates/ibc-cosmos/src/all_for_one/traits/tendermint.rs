use ibc::core::ics23_commitment::merkle::MerkleProof;
use ibc::core::ics24_host::identifier::ClientId;
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_framework::all_for_one::traits::base::AfoChainContext;
use ibc_framework::core::traits::error::InjectError;
use ibc_framework::core::traits::stores::client_reader::HasClientReader;
use ibc_proto::google::protobuf::Any;

use crate::clients::tendermint::client::{
    TendermintClient, TendermintClientHeader, TendermintClientState, TendermintConsensusState,
    TendermintMisbehavior,
};
use crate::clients::tendermint::update_client::Error as UpdateTendermintClientError;

pub trait AfoTendermintOnlyChainContext:
    AfoChainContext<
        Height = Height,
        Timestamp = Timestamp,
        Message = Any,
        ClientId = ClientId,
        MerkleProof = MerkleProof,
        AnyClientState = TendermintClientState,
        AnyConsensusState = TendermintConsensusState,
        AnyClientHeader = TendermintClientHeader,
        AnyMisbehavior = TendermintMisbehavior,
    > + InjectError<UpdateTendermintClientError>
    + HasClientReader<TendermintClient>
{
}

impl<Context> AfoTendermintOnlyChainContext for Context where
    Context: AfoChainContext<
            Height = Height,
            Timestamp = Timestamp,
            Message = Any,
            ClientId = ClientId,
            MerkleProof = MerkleProof,
            AnyClientState = TendermintClientState,
            AnyConsensusState = TendermintConsensusState,
            AnyClientHeader = TendermintClientHeader,
            AnyMisbehavior = TendermintMisbehavior,
        > + InjectError<UpdateTendermintClientError>
        + HasClientReader<TendermintClient>
{
}
