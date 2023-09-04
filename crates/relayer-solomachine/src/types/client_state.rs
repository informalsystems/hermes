use eyre::eyre;

use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::lightclients::solomachine::v3::ClientState as ProtoClientState;
use ibc_proto::protobuf::Protobuf;
use ibc_relayer_types::keys::ROUTER_KEY;
use ibc_relayer_types::tx_msg::Msg;
use prost::Message;

use crate::types::consensus_state::SolomachineConsensusState;
use crate::types::error::{BaseError, Error};

const TYPE_URL: &str = "/ibc.lightclients.solomachine.v3.ClientState";

#[derive(Clone, Debug)]
pub struct SolomachineClientState {
    pub sequence: u64,
    pub is_frozen: bool,
    pub consensus_state: SolomachineConsensusState,
}

impl TryFrom<Any> for SolomachineClientState {
    type Error = Error;

    fn try_from(raw: Any) -> Result<Self, Error> {
        use bytes::Buf;
        use core::ops::Deref;

        fn decode_client_state<B: Buf>(buf: B) -> Result<SolomachineClientState, Error> {
            ProtoClientState::decode(buf)
                .map_err(|e| BaseError::generic(eyre!("error decoding client state: {e}")))?
                .try_into()
        }

        match raw.type_url.as_str() {
            TYPE_URL => decode_client_state(raw.value.deref()).map_err(Into::into),
            _ => Err(BaseError::generic(eyre!("unknown client state: {}", raw.type_url)).into()),
        }
    }
}

impl Msg for SolomachineClientState {
    type ValidationError = Error;
    type Raw = ProtoClientState;

    fn route(&self) -> String {
        ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}

impl Protobuf<ProtoClientState> for SolomachineClientState {}

impl TryFrom<ProtoClientState> for SolomachineClientState {
    type Error = Error;

    fn try_from(value: ProtoClientState) -> Result<Self, Self::Error> {
        let consensus_state = value.consensus_state.unwrap().try_into().unwrap();

        Ok(SolomachineClientState {
            sequence: value.sequence,
            is_frozen: value.is_frozen,
            consensus_state,
        })
    }
}

impl From<SolomachineClientState> for ProtoClientState {
    fn from(value: SolomachineClientState) -> Self {
        ProtoClientState {
            sequence: value.sequence,
            is_frozen: value.is_frozen,
            consensus_state: Some(value.consensus_state.into()),
            //allow_update_after_proposal: true,
        }
    }
}

pub fn decode_client_state(buf: &[u8]) -> SolomachineClientState {
    let any_value = Any::decode(buf).unwrap();
    let proto_state = ProtoClientState::decode(any_value.value.as_ref()).unwrap();

    let client_state = proto_state.try_into().unwrap();

    client_state
}
