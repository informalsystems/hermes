use ibc_relayer_types::clients::ics07_tendermint::client_state::ClientState;
use ibc_relayer_types::clients::ics07_tendermint::consensus_state::ConsensusState;
use ibc_relayer_types::clients::ics07_tendermint::header::Header as TendermintHeader;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;

pub struct CosmosCreateClientEvent {
    pub client_id: ClientId,
}

pub struct CosmosUpdateClientPayload {
    pub headers: Vec<TendermintHeader>,
}

pub struct CosmosCreateClientPayload {
    pub client_state: ClientState,
    pub consensus_state: ConsensusState,
}
