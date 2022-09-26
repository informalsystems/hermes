use core::time::Duration;

use ibc_proto::ibc::core::client::v1::IdentifiedClientState;
use ibc_proto::ibc::core::commitment::v1::MerkleProof;
use ibc_proto::ibc::lightclients::tendermint::v1::ClientState as RawClientState;
#[cfg(test)]
use ibc_proto::ibc::mock::ClientState as RawMockClientState;
use ibc_proto::protobuf::Protobuf;
use serde::{Deserialize, Serialize};

use ibc::clients::ics07_tendermint::client_state::{
    ClientState as TmClientState, UpgradeOptions as TmUpgradeOptions,
    TENDERMINT_CLIENT_STATE_TYPE_URL,
};
use ibc::core::ics02_client::client_state::{
    downcast_client_state, ClientState, UpdatedState, UpgradeOptions,
};
use ibc::core::ics02_client::client_type::ClientType;
use ibc::core::ics02_client::consensus_state::ConsensusState;
use ibc::core::ics02_client::context::ClientReader;
use ibc::core::ics02_client::error::Error;
use ibc::core::ics02_client::trust_threshold::TrustThreshold;
use ibc::core::ics03_connection::connection::ConnectionEnd;
use ibc::core::ics04_channel::channel::ChannelEnd;
use ibc::core::ics04_channel::commitment::{AcknowledgementCommitment, PacketCommitment};
use ibc::core::ics04_channel::context::ChannelReader;
use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics23_commitment::commitment::{
    CommitmentPrefix, CommitmentProofBytes, CommitmentRoot,
};
use ibc::core::ics24_host::error::ValidationError;
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
#[cfg(test)]
use ibc::mock::client_state::MockClientState;
#[cfg(test)]
use ibc::mock::client_state::MOCK_CLIENT_STATE_TYPE_URL;
use ibc::Height;
use ibc_proto::google::protobuf::Any;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum AnyUpgradeOptions {
    Tendermint(TmUpgradeOptions),

    #[cfg(test)]
    Mock(()),
}

impl AnyUpgradeOptions {
    fn as_tm_upgrade_options(&self) -> Option<&TmUpgradeOptions> {
        match self {
            AnyUpgradeOptions::Tendermint(tm) => Some(tm),
            #[cfg(test)]
            AnyUpgradeOptions::Mock(_) => None,
        }
    }
}

impl UpgradeOptions for AnyUpgradeOptions {}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum AnyClientState {
    Tendermint(TmClientState),

    #[cfg(test)]
    Mock(MockClientState),
}

impl AnyClientState {
    pub fn latest_height(&self) -> Height {
        match self {
            Self::Tendermint(tm_state) => tm_state.latest_height(),

            #[cfg(test)]
            Self::Mock(mock_state) => mock_state.latest_height(),
        }
    }

    pub fn frozen_height(&self) -> Option<Height> {
        match self {
            Self::Tendermint(tm_state) => tm_state.frozen_height(),

            #[cfg(test)]
            Self::Mock(mock_state) => mock_state.frozen_height(),
        }
    }

    pub fn trust_threshold(&self) -> Option<TrustThreshold> {
        match self {
            AnyClientState::Tendermint(state) => Some(state.trust_level),

            #[cfg(test)]
            AnyClientState::Mock(_) => None,
        }
    }

    pub fn max_clock_drift(&self) -> Duration {
        match self {
            AnyClientState::Tendermint(state) => state.max_clock_drift,

            #[cfg(test)]
            AnyClientState::Mock(_) => Duration::new(0, 0),
        }
    }

    pub fn client_type(&self) -> ClientType {
        match self {
            Self::Tendermint(state) => state.client_type(),

            #[cfg(test)]
            Self::Mock(state) => state.client_type(),
        }
    }

    pub fn refresh_period(&self) -> Option<Duration> {
        match self {
            AnyClientState::Tendermint(tm_state) => tm_state.refresh_time(),

            #[cfg(test)]
            AnyClientState::Mock(mock_state) => mock_state.refresh_time(),
        }
    }
}

impl Protobuf<Any> for AnyClientState {}

impl TryFrom<Any> for AnyClientState {
    type Error = Error;

    fn try_from(raw: Any) -> Result<Self, Self::Error> {
        match raw.type_url.as_str() {
            "" => Err(Error::empty_client_state_response()),

            TENDERMINT_CLIENT_STATE_TYPE_URL => Ok(AnyClientState::Tendermint(
                Protobuf::<RawClientState>::decode_vec(&raw.value)
                    .map_err(Error::decode_raw_client_state)?,
            )),

            #[cfg(test)]
            MOCK_CLIENT_STATE_TYPE_URL => Ok(AnyClientState::Mock(
                Protobuf::<RawMockClientState>::decode_vec(&raw.value)
                    .map_err(Error::decode_raw_client_state)?,
            )),

            _ => Err(Error::unknown_client_state_type(raw.type_url)),
        }
    }
}

impl From<AnyClientState> for Any {
    fn from(value: AnyClientState) -> Self {
        match value {
            AnyClientState::Tendermint(value) => Any {
                type_url: TENDERMINT_CLIENT_STATE_TYPE_URL.to_string(),
                value: Protobuf::<RawClientState>::encode_vec(&value)
                    .expect("encoding to `Any` from `AnyClientState::Tendermint`"),
            },
            #[cfg(test)]
            AnyClientState::Mock(value) => Any {
                type_url: MOCK_CLIENT_STATE_TYPE_URL.to_string(),
                value: Protobuf::<RawMockClientState>::encode_vec(&value)
                    .expect("encoding to `Any` from `AnyClientState::Mock`"),
            },
        }
    }
}

impl ClientState for AnyClientState {
    fn chain_id(&self) -> ChainId {
        match self {
            AnyClientState::Tendermint(tm_state) => tm_state.chain_id(),

            #[cfg(test)]
            AnyClientState::Mock(mock_state) => mock_state.chain_id(),
        }
    }

    fn client_type(&self) -> ClientType {
        self.client_type()
    }

    fn latest_height(&self) -> Height {
        self.latest_height()
    }

    fn frozen_height(&self) -> Option<Height> {
        self.frozen_height()
    }

    fn upgrade(
        &mut self,
        upgrade_height: Height,
        upgrade_options: &dyn UpgradeOptions,
        chain_id: ChainId,
    ) {
        let upgrade_options = upgrade_options
            .as_any()
            .downcast_ref::<AnyUpgradeOptions>()
            .expect("UpgradeOptions not of type AnyUpgradeOptions");
        match self {
            AnyClientState::Tendermint(tm_state) => tm_state.upgrade(
                upgrade_height,
                upgrade_options.as_tm_upgrade_options().unwrap(),
                chain_id,
            ),

            #[cfg(test)]
            AnyClientState::Mock(mock_state) => {
                mock_state.upgrade(upgrade_height, upgrade_options, chain_id)
            }
        }
    }

    fn expired(&self, elapsed_since_latest: Duration) -> bool {
        match self {
            AnyClientState::Tendermint(tm_state) => tm_state.expired(elapsed_since_latest),

            #[cfg(test)]
            AnyClientState::Mock(mock_state) => mock_state.expired(elapsed_since_latest),
        }
    }

    fn initialise(&self, _consensus_state: Any) -> Result<Box<dyn ConsensusState>, Error> {
        unimplemented!()
    }

    fn check_header_and_update_state(
        &self,
        _ctx: &dyn ClientReader,
        _client_id: ClientId,
        _header: Any,
    ) -> Result<UpdatedState, Error> {
        unimplemented!()
    }

    fn verify_upgrade_and_update_state(
        &self,
        _consensus_state: Any,
        _proof_upgrade_client: MerkleProof,
        _proof_upgrade_consensus_state: MerkleProof,
    ) -> Result<UpdatedState, Error> {
        unimplemented!()
    }

    fn verify_client_consensus_state(
        &self,
        _height: Height,
        _prefix: &CommitmentPrefix,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _client_id: &ClientId,
        _consensus_height: Height,
        _expected_consensus_state: &dyn ConsensusState,
    ) -> Result<(), Error> {
        unimplemented!()
    }

    fn verify_connection_state(
        &self,
        _height: Height,
        _prefix: &CommitmentPrefix,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _connection_id: &ConnectionId,
        _expected_connection_end: &ConnectionEnd,
    ) -> Result<(), Error> {
        unimplemented!()
    }

    fn verify_channel_state(
        &self,
        _height: Height,
        _prefix: &CommitmentPrefix,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _expected_channel_end: &ChannelEnd,
    ) -> Result<(), Error> {
        unimplemented!()
    }

    fn verify_client_full_state(
        &self,
        _height: Height,
        _prefix: &CommitmentPrefix,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _client_id: &ClientId,
        _expected_client_state: Any,
    ) -> Result<(), Error> {
        unimplemented!()
    }

    fn verify_packet_data(
        &self,
        _ctx: &dyn ChannelReader,
        _height: Height,
        _connection_end: &ConnectionEnd,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _sequence: Sequence,
        _commitment: PacketCommitment,
    ) -> Result<(), Error> {
        unimplemented!()
    }

    fn verify_packet_acknowledgement(
        &self,
        _ctx: &dyn ChannelReader,
        _height: Height,
        _connection_end: &ConnectionEnd,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _sequence: Sequence,
        _ack: AcknowledgementCommitment,
    ) -> Result<(), Error> {
        unimplemented!()
    }

    fn verify_next_sequence_recv(
        &self,
        _ctx: &dyn ChannelReader,
        _height: Height,
        _connection_end: &ConnectionEnd,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _sequence: Sequence,
    ) -> Result<(), Error> {
        unimplemented!()
    }

    fn verify_packet_receipt_absence(
        &self,
        _ctx: &dyn ChannelReader,
        _height: Height,
        _connection_end: &ConnectionEnd,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _sequence: Sequence,
    ) -> Result<(), Error> {
        unimplemented!()
    }
}

impl From<TmClientState> for AnyClientState {
    fn from(cs: TmClientState) -> Self {
        Self::Tendermint(cs)
    }
}

#[cfg(test)]
impl From<MockClientState> for AnyClientState {
    fn from(cs: MockClientState) -> Self {
        Self::Mock(cs)
    }
}

impl From<&dyn ClientState> for AnyClientState {
    fn from(client_state: &dyn ClientState) -> Self {
        #[cfg(test)]
        if let Some(cs) = downcast_client_state::<MockClientState>(client_state) {
            return AnyClientState::from(*cs);
        }

        if let Some(cs) = downcast_client_state::<TmClientState>(client_state) {
            AnyClientState::from(cs.clone())
        } else {
            unreachable!()
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub struct IdentifiedAnyClientState {
    pub client_id: ClientId,
    pub client_state: AnyClientState,
}

impl IdentifiedAnyClientState {
    pub fn new(client_id: ClientId, client_state: AnyClientState) -> Self {
        IdentifiedAnyClientState {
            client_id,
            client_state,
        }
    }
}

impl Protobuf<IdentifiedClientState> for IdentifiedAnyClientState {}

impl TryFrom<IdentifiedClientState> for IdentifiedAnyClientState {
    type Error = Error;

    fn try_from(raw: IdentifiedClientState) -> Result<Self, Self::Error> {
        Ok(IdentifiedAnyClientState {
            client_id: raw.client_id.parse().map_err(|e: ValidationError| {
                Error::invalid_raw_client_id(raw.client_id.clone(), e)
            })?,
            client_state: raw
                .client_state
                .ok_or_else(Error::missing_raw_client_state)?
                .try_into()?,
        })
    }
}

impl From<IdentifiedAnyClientState> for IdentifiedClientState {
    fn from(value: IdentifiedAnyClientState) -> Self {
        IdentifiedClientState {
            client_id: value.client_id.to_string(),
            client_state: Some(value.client_state.into()),
        }
    }
}

#[cfg(test)]
mod tests {
    use ibc::clients::ics07_tendermint::client_state::test_util::get_dummy_tendermint_client_state;
    use ibc::clients::ics07_tendermint::header::test_util::get_dummy_tendermint_header;
    use ibc_proto::google::protobuf::Any;
    use test_log::test;

    use super::AnyClientState;

    #[test]
    fn any_client_state_serialization() {
        let tm_client_state: AnyClientState =
            get_dummy_tendermint_client_state(get_dummy_tendermint_header()).into();

        let raw: Any = tm_client_state.clone().into();
        let tm_client_state_back = AnyClientState::try_from(raw).unwrap();
        assert_eq!(tm_client_state, tm_client_state_back);
    }
}
