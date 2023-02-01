use crate::core::traits::error::HasError;
use crate::core::traits::host::HasHostTypes;
use crate::core::traits::prism::Prism;
use crate::core::traits::sync::Async;

pub trait HasAnyClientTypes: Async {
    type ClientType: Eq + Async;

    type AnyClientState: Async;

    type AnyConsensusState: Async;

    type AnyClientHeader: Async;

    type AnyMisbehavior: Async;
}

pub trait HasAnyClientMethods: HasAnyClientTypes + HasHostTypes {
    fn client_state_type(client_state: &Self::AnyClientState) -> Self::ClientType;

    fn client_state_is_frozen(client_state: &Self::AnyClientState) -> bool;

    fn client_state_trusting_period(client_state: &Self::AnyClientState) -> Self::Duration;

    fn client_state_latest_height(client_state: &Self::AnyClientState) -> Self::Height;

    fn consensus_state_timestamp(consensus_state: &Self::AnyConsensusState) -> Self::Timestamp;

    fn client_header_height(client_header: &Self::AnyClientHeader) -> Self::Height;
}

pub trait HasClientTypes: Async {
    type ClientState: Async;

    type ConsensusState: Async;

    type ClientHeader: Async;

    type Misbehavior: Async;
}

pub trait HasClientTypeFor<Client>: HasAnyClientTypes {
    const CLIENT_TYPE: Self::ClientType;
}

pub trait InjectClientTypeMismatchError: HasError + HasAnyClientTypes {
    fn client_type_mismatch_error(expected_client_type: &Self::ClientType) -> Self::Error;
}

pub trait HasClientPrisms<Client>:
    HasAnyClientTypes
    + Prism<Self::AnyClientState, Client::ClientState>
    + Prism<Self::AnyConsensusState, Client::ConsensusState>
    + Prism<Self::AnyClientHeader, Client::ClientHeader>
    + Prism<Self::AnyMisbehavior, Client::Misbehavior>
    + HasError
where
    Client: HasClientTypes,
{
    fn into_any_client_state(client_state: Client::ClientState) -> Self::AnyClientState;

    fn try_from_any_client_state(
        client_state: Self::AnyClientState,
    ) -> Result<Client::ClientState, Self::Error>;

    fn try_from_any_client_state_ref(
        client_state: &Self::AnyClientState,
    ) -> Result<&Client::ClientState, Self::Error>;

    fn into_any_consensus_state(consensus_state: Client::ConsensusState)
        -> Self::AnyConsensusState;

    fn try_from_any_consensus_state(
        consensus_state: Self::AnyConsensusState,
    ) -> Result<Client::ConsensusState, Self::Error>;

    fn try_from_any_consensus_state_ref(
        consensus_state: &Self::AnyConsensusState,
    ) -> Result<&Client::ConsensusState, Self::Error>;

    fn into_any_client_header(client_header: Client::ClientHeader) -> Self::AnyClientHeader;

    fn try_from_any_client_header(
        client_header: Self::AnyClientHeader,
    ) -> Result<Client::ClientHeader, Self::Error>;

    fn try_from_any_client_header_ref(
        client_header: &Self::AnyClientHeader,
    ) -> Result<&Client::ClientHeader, Self::Error>;

    fn into_any_misbehavior(misbehavior: Client::Misbehavior) -> Self::AnyMisbehavior;

    fn try_from_any_misbehavior(
        misbehavior: Self::AnyMisbehavior,
    ) -> Result<Client::Misbehavior, Self::Error>;

    fn try_from_any_misbehavior_ref(
        misbehavior: &Self::AnyMisbehavior,
    ) -> Result<&Client::Misbehavior, Self::Error>;
}

impl<Context, Client> HasClientPrisms<Client> for Context
where
    Context: HasClientTypeFor<Client>,
    Client: HasClientTypes,
    Context: InjectClientTypeMismatchError,
    Context: Prism<Self::AnyClientState, Client::ClientState>
        + Prism<Self::AnyConsensusState, Client::ConsensusState>
        + Prism<Self::AnyClientHeader, Client::ClientHeader>
        + Prism<Self::AnyMisbehavior, Client::Misbehavior>,
{
    fn into_any_client_state(client_state: Client::ClientState) -> Self::AnyClientState {
        Context::into(client_state)
    }

    fn try_from_any_client_state(
        client_state: Self::AnyClientState,
    ) -> Result<Client::ClientState, Context::Error> {
        Context::try_from(client_state)
            .ok_or_else(|| Context::client_type_mismatch_error(&Self::CLIENT_TYPE))
    }

    fn try_from_any_client_state_ref(
        client_state: &Self::AnyClientState,
    ) -> Result<&Client::ClientState, Context::Error> {
        Context::try_from_ref(client_state)
            .ok_or_else(|| Context::client_type_mismatch_error(&Self::CLIENT_TYPE))
    }

    fn into_any_consensus_state(
        consensus_state: Client::ConsensusState,
    ) -> Self::AnyConsensusState {
        Context::into(consensus_state)
    }

    fn try_from_any_consensus_state(
        consensus_state: Self::AnyConsensusState,
    ) -> Result<Client::ConsensusState, Context::Error> {
        Context::try_from(consensus_state)
            .ok_or_else(|| Context::client_type_mismatch_error(&Self::CLIENT_TYPE))
    }

    fn try_from_any_consensus_state_ref(
        consensus_state: &Self::AnyConsensusState,
    ) -> Result<&Client::ConsensusState, Context::Error> {
        Context::try_from_ref(consensus_state)
            .ok_or_else(|| Context::client_type_mismatch_error(&Self::CLIENT_TYPE))
    }

    fn into_any_client_header(client_header: Client::ClientHeader) -> Self::AnyClientHeader {
        Context::into(client_header)
    }

    fn try_from_any_client_header(
        client_header: Self::AnyClientHeader,
    ) -> Result<Client::ClientHeader, Context::Error> {
        Context::try_from(client_header)
            .ok_or_else(|| Context::client_type_mismatch_error(&Self::CLIENT_TYPE))
    }

    fn try_from_any_client_header_ref(
        client_header: &Self::AnyClientHeader,
    ) -> Result<&Client::ClientHeader, Context::Error> {
        Context::try_from_ref(client_header)
            .ok_or_else(|| Context::client_type_mismatch_error(&Self::CLIENT_TYPE))
    }

    fn into_any_misbehavior(misbehavior: Client::Misbehavior) -> Self::AnyMisbehavior {
        Context::into(misbehavior)
    }

    fn try_from_any_misbehavior(
        misbehavior: Self::AnyMisbehavior,
    ) -> Result<Client::Misbehavior, Context::Error> {
        Context::try_from(misbehavior)
            .ok_or_else(|| Context::client_type_mismatch_error(&Self::CLIENT_TYPE))
    }

    fn try_from_any_misbehavior_ref(
        misbehavior: &Self::AnyMisbehavior,
    ) -> Result<&Client::Misbehavior, Context::Error> {
        Context::try_from_ref(misbehavior)
            .ok_or_else(|| Context::client_type_mismatch_error(&Self::CLIENT_TYPE))
    }
}

pub trait ContainsClient<Client>:
    HasAnyClientTypes + HasClientPrisms<Client> + HasClientTypeFor<Client>
where
    Client: HasClientTypes,
{
}

impl<Context, Client> ContainsClient<Client> for Context
where
    Client: HasClientTypes,
    Context: HasAnyClientTypes + HasClientPrisms<Client> + HasClientTypeFor<Client>,
{
}
