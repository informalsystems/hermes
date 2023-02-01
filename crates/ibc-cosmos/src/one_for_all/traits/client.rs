use core::time::Duration;
use ibc::clients::ics07_tendermint::client_state::ClientState as TendermintClientState;
use ibc::clients::ics07_tendermint::consensus_state::ConsensusState as TendermintConsensusState;
use ibc::clients::ics07_tendermint::header::Header as TendermintClientHeader;
use ibc::clients::ics07_tendermint::misbehaviour::Misbehaviour as TendermintMisbehavior;
use ibc::core::ics02_client::client_type::ClientType;
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_framework::core::traits::sync::Async;

pub trait OfaCosmosClient: Async {
    type AnyClientState: Async;

    type AnyConsensusState: Async;

    type AnyClientHeader: Async;

    type AnyMisbehavior: Async;

    fn client_state_type(client_state: &Self::AnyClientState) -> ClientType;

    fn client_state_is_frozen(client_state: &Self::AnyClientState) -> bool;

    fn client_state_trusting_period(client_state: &Self::AnyClientState) -> Duration;

    fn client_state_latest_height(client_state: &Self::AnyClientState) -> Height;

    fn consensus_state_timestamp(consensus_state: &Self::AnyConsensusState) -> Timestamp;

    fn client_header_height(client_header: &Self::AnyClientHeader) -> Height;

    fn try_into_tendermint_client_state(
        client_state: Self::AnyClientState,
    ) -> Option<TendermintClientState>;

    fn try_into_tendermint_client_state_ref(
        client_state: &Self::AnyClientState,
    ) -> Option<&TendermintClientState>;

    fn from_tendermint_client_state(client_state: TendermintClientState) -> Self::AnyClientState;

    fn try_into_tendermint_consensus_state(
        consensus_state: Self::AnyConsensusState,
    ) -> Option<TendermintConsensusState>;

    fn try_into_tendermint_consensus_state_ref(
        consensus_state: &Self::AnyConsensusState,
    ) -> Option<&TendermintConsensusState>;

    fn from_tendermint_consensus_state(
        consensus_state: TendermintConsensusState,
    ) -> Self::AnyConsensusState;

    fn try_into_tendermint_client_header(
        client_header: Self::AnyClientHeader,
    ) -> Option<TendermintClientHeader>;

    fn try_into_tendermint_client_header_ref(
        client_header: &Self::AnyClientHeader,
    ) -> Option<&TendermintClientHeader>;

    fn from_tendermint_client_header(
        client_header: TendermintClientHeader,
    ) -> Self::AnyClientHeader;

    fn try_into_tendermint_misbehavior(
        misbehavior: Self::AnyMisbehavior,
    ) -> Option<TendermintMisbehavior>;

    fn try_into_tendermint_misbehavior_ref(
        misbehavior: &Self::AnyMisbehavior,
    ) -> Option<&TendermintMisbehavior>;

    fn from_tendermint_misbehavior(misbehavior: TendermintMisbehavior) -> Self::AnyMisbehavior;
}
