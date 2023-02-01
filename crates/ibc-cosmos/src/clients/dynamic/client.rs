use core::time::Duration;
use ibc::clients::ics07_tendermint::client_state::ClientState as TendermintClientState;
use ibc::clients::ics07_tendermint::consensus_state::ConsensusState as TendermintConsensusState;
use ibc::clients::ics07_tendermint::header::Header as TendermintClientHeader;
use ibc::clients::ics07_tendermint::misbehaviour::Misbehaviour as TendermintMisbehavior;
use ibc::core::ics02_client::client_state::ClientState;
use ibc::core::ics02_client::client_type::ClientType;
use ibc::core::ics02_client::consensus_state::ConsensusState;
use ibc::core::ics02_client::header::Header as ClientHeader;
use ibc::core::ics02_client::misbehaviour::Misbehaviour;
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_framework::core::traits::client::{
    HasAnyClientMethods, HasAnyClientTypes, HasClientTypeFor,
};
use ibc_framework::core::traits::host::HasHostTypes;
use ibc_framework::core::traits::prism::Prism;

use crate::clients::tendermint::client::TendermintClient;

pub struct DynamicClient;

pub struct DynClientState {
    pub client_state: Box<dyn ClientState>,
}

pub struct DynConsensusState {
    pub consensus_state: Box<dyn ConsensusState>,
}

pub struct DynClientHeader {
    pub client_header: Box<dyn ClientHeader>,
}

pub struct DynMisbehavior {
    pub misbehavior: Box<dyn Misbehaviour>,
}

impl HasAnyClientTypes for DynamicClient {
    type ClientType = ClientType;

    type AnyClientState = DynClientState;

    type AnyConsensusState = DynConsensusState;

    type AnyClientHeader = DynClientHeader;

    type AnyMisbehavior = DynMisbehavior;
}

impl Prism<DynClientState, TendermintClientState> for DynamicClient {
    fn into(client_state: TendermintClientState) -> DynClientState {
        DynClientState::new(client_state)
    }

    fn try_from(client_state: DynClientState) -> Option<TendermintClientState> {
        Self::try_from_ref(&client_state).cloned()
    }

    fn try_from_ref(client_state: &DynClientState) -> Option<&TendermintClientState> {
        client_state.client_state.as_any().downcast_ref()
    }
}

impl Prism<DynConsensusState, TendermintConsensusState> for DynamicClient {
    fn into(consensus_state: TendermintConsensusState) -> DynConsensusState {
        DynConsensusState::new(consensus_state)
    }

    fn try_from(consensus_state: DynConsensusState) -> Option<TendermintConsensusState> {
        Self::try_from_ref(&consensus_state).cloned()
    }

    fn try_from_ref(consensus_state: &DynConsensusState) -> Option<&TendermintConsensusState> {
        consensus_state.consensus_state.as_any().downcast_ref()
    }
}

impl Prism<DynClientHeader, TendermintClientHeader> for DynamicClient {
    fn into(client_header: TendermintClientHeader) -> DynClientHeader {
        DynClientHeader::new(client_header)
    }

    fn try_from(client_header: DynClientHeader) -> Option<TendermintClientHeader> {
        Self::try_from_ref(&client_header).cloned()
    }

    fn try_from_ref(client_header: &DynClientHeader) -> Option<&TendermintClientHeader> {
        client_header.client_header.as_any().downcast_ref()
    }
}

impl Prism<DynMisbehavior, TendermintMisbehavior> for DynamicClient {
    fn into(misbehavior: TendermintMisbehavior) -> DynMisbehavior {
        DynMisbehavior::new(misbehavior)
    }

    fn try_from(misbehavior: DynMisbehavior) -> Option<TendermintMisbehavior> {
        Self::try_from_ref(&misbehavior).cloned()
    }

    fn try_from_ref(misbehavior: &DynMisbehavior) -> Option<&TendermintMisbehavior> {
        misbehavior.misbehavior.as_any().downcast_ref()
    }
}

impl HasClientTypeFor<TendermintClient> for DynamicClient {
    const CLIENT_TYPE: ClientType = ClientType::Tendermint;
}

impl HasHostTypes for DynamicClient {
    type Height = Height;

    type Timestamp = Timestamp;

    type Duration = Duration;
}

impl HasAnyClientMethods for DynamicClient {
    fn client_state_type(client_state: &DynClientState) -> Self::ClientType {
        client_state.client_state.client_type()
    }

    fn client_state_is_frozen(client_state: &DynClientState) -> bool {
        client_state.client_state.is_frozen()
    }

    fn client_state_trusting_period(client_state: &DynClientState) -> Self::Duration {
        client_state.client_state.trusting_period()
    }

    fn client_state_latest_height(client_state: &DynClientState) -> Self::Height {
        client_state.client_state.latest_height()
    }

    fn consensus_state_timestamp(consensus_state: &DynConsensusState) -> Self::Timestamp {
        consensus_state.consensus_state.timestamp()
    }

    fn client_header_height(client_header: &DynClientHeader) -> Self::Height {
        client_header.client_header.height()
    }
}

impl DynClientState {
    fn new(client_state: impl ClientState) -> Self {
        Self {
            client_state: Box::new(client_state),
        }
    }
}

impl DynConsensusState {
    fn new(consensus_state: impl ConsensusState) -> Self {
        Self {
            consensus_state: Box::new(consensus_state),
        }
    }
}

impl DynClientHeader {
    fn new(client_header: impl ClientHeader) -> Self {
        Self {
            client_header: Box::new(client_header),
        }
    }
}

impl DynMisbehavior {
    fn new(misbehavior: impl Misbehaviour) -> Self {
        Self {
            misbehavior: Box::new(misbehavior),
        }
    }
}
