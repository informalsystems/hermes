use prost_amino_derive::Message;

#[derive(Clone, PartialEq, Message)]
// TODO: remove when the sdk switches to vanilla proto
#[amino_name = "ibc/client/tendermint/ClientState"]
struct ClientState {
    #[prost_amino(string, tag = "1")]
    pub id: String,

    #[prost_amino(int64, tag = "2")]
    pub trusting_period: i64,

    #[prost_amino(int64, tag = "3")]
    pub unbonding_period: i64,

    #[prost_amino(uint64, tag = "4")]
    pub frozen_height: crate::Height,

    // TODO: remove `amino_name` annotation as soon as this is actually protobuf
    #[prost_amino(message, tag = "5",  amino_name = "ibc/client/tendermint/Header")]
    pub latest_header: Option<Header>,
}
// ---------------------------------------------------------------------
// TODO: these types below should actually live in tendermint-rs!
// under tendermint/src/amino_types/
// these should be re-used here
// see: https://github.com/informalsystems/tendermint-rs/issues/203
// ---------------------------------------------------------------------

#[derive(Clone, PartialEq, Message)]
pub struct Header {
    // pub signed_header: SignedHeader,
    // pub validator_set: ValidatorSet,
    // pub next_validator_set: ValidatorSet,
}
