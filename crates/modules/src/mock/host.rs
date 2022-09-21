//! Host chain types and methods, used by context mock.

use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::lightclients::tendermint::v1::Header as RawHeader;
use ibc_proto::protobuf::Protobuf as ErasedProtobuf;
use serde::Serialize;
use tendermint::block::Header as TmHeader;
use tendermint_testgen::light_block::TmLightBlock;
use tendermint_testgen::{Generator, LightBlock as TestgenLightBlock};

use crate::clients::ics07_tendermint::consensus_state::ConsensusState as TMConsensusState;
use crate::clients::ics07_tendermint::header::TENDERMINT_HEADER_TYPE_URL;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::consensus_state::ConsensusState;
use crate::core::ics02_client::error::Error;
use crate::core::ics02_client::header::Header;
use crate::core::ics24_host::identifier::ChainId;
use crate::mock::consensus_state::MockConsensusState;
use crate::mock::header::MockHeader;
use crate::prelude::*;
use crate::timestamp::Timestamp;
use crate::Height;

/// Defines the different types of host chains that a mock context can emulate.
/// The variants are as follows:
/// - `Mock` defines that the context history consists of `MockHeader` blocks.
/// - `SyntheticTendermint`: the context has synthetically-generated Tendermint (light) blocks.
/// See also the `HostBlock` enum to get more insights into the underlying block type.
#[derive(Clone, Debug, Copy)]
pub enum HostType {
    Mock,
    SyntheticTendermint,
}

#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct SyntheticTmBlock {
    pub trusted_height: Height,
    pub light_block: TmLightBlock,
}

impl SyntheticTmBlock {
    pub fn header(&self) -> &TmHeader {
        &self.light_block.signed_header.header
    }
}

/// Depending on `HostType` (the type of host chain underlying a context mock), this enum defines
/// the type of blocks composing the history of the host chain.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub enum HostBlock {
    Mock(MockHeader),
    SyntheticTendermint(SyntheticTmBlock),
}

impl HostBlock {
    /// Returns the height of a block.
    pub fn height(&self) -> Height {
        match self {
            HostBlock::Mock(header) => header.height(),
            HostBlock::SyntheticTendermint(light_block) => Height::new(
                ChainId::chain_version(light_block.header().chain_id.as_str()),
                light_block.header().height.value(),
            )
            .unwrap(),
        }
    }

    pub fn set_trusted_height(&mut self, height: Height) {
        match self {
            HostBlock::Mock(_) => {}
            HostBlock::SyntheticTendermint(light_block) => light_block.trusted_height = height,
        }
    }

    /// Returns the timestamp of a block.
    pub fn timestamp(&self) -> Timestamp {
        match self {
            HostBlock::Mock(header) => header.timestamp,
            HostBlock::SyntheticTendermint(light_block) => light_block.header().time.into(),
        }
    }

    /// Generates a new block at `height` for the given chain identifier and chain type.
    pub fn generate_block(
        chain_id: ChainId,
        chain_type: HostType,
        height: u64,
        timestamp: Timestamp,
    ) -> HostBlock {
        match chain_type {
            HostType::Mock => HostBlock::Mock(MockHeader {
                height: Height::new(chain_id.version(), height).unwrap(),
                timestamp,
            }),
            HostType::SyntheticTendermint => {
                HostBlock::SyntheticTendermint(Self::generate_tm_block(chain_id, height, timestamp))
            }
        }
    }

    pub fn generate_tm_block(
        chain_id: ChainId,
        height: u64,
        timestamp: Timestamp,
    ) -> SyntheticTmBlock {
        let light_block = TestgenLightBlock::new_default_with_time_and_chain_id(
            chain_id.to_string(),
            timestamp.into_tm_time().unwrap(),
            height,
        )
        .generate()
        .unwrap();
        SyntheticTmBlock {
            trusted_height: Height::new(chain_id.version(), 1).unwrap(),
            light_block,
        }
    }
}

impl From<SyntheticTmBlock> for Box<dyn ConsensusState> {
    fn from(light_block: SyntheticTmBlock) -> Self {
        let cs = TMConsensusState::from(light_block.header().clone());
        cs.into_box()
    }
}

impl From<HostBlock> for Box<dyn ConsensusState> {
    fn from(any_block: HostBlock) -> Self {
        match any_block {
            HostBlock::Mock(mock_header) => MockConsensusState::new(mock_header).into_box(),
            HostBlock::SyntheticTendermint(light_block) => {
                TMConsensusState::from(light_block.header().clone()).into_box()
            }
        }
    }
}

impl ErasedProtobuf<Any> for HostBlock {}

impl TryFrom<Any> for HostBlock {
    type Error = Error;

    fn try_from(_raw: Any) -> Result<Self, Error> {
        todo!()
    }
}

impl From<HostBlock> for Any {
    fn from(value: HostBlock) -> Self {
        fn encode_light_block(light_block: SyntheticTmBlock) -> Vec<u8> {
            use prost::Message;

            let SyntheticTmBlock {
                trusted_height,
                light_block,
            } = light_block;

            RawHeader {
                signed_header: Some(light_block.signed_header.into()),
                validator_set: Some(light_block.validators.into()),
                trusted_height: Some(trusted_height.into()),
                trusted_validators: Some(light_block.next_validators.into()),
            }
            .encode_to_vec()
        }

        match value {
            HostBlock::Mock(mock_header) => mock_header.into(),
            HostBlock::SyntheticTendermint(light_block_box) => Self {
                type_url: TENDERMINT_HEADER_TYPE_URL.to_string(),
                value: encode_light_block(light_block_box),
            },
        }
    }
}

impl Header for HostBlock {
    fn client_type(&self) -> ClientType {
        match self {
            HostBlock::Mock(_) => ClientType::Mock,
            HostBlock::SyntheticTendermint(_) => ClientType::Tendermint,
        }
    }

    fn height(&self) -> Height {
        HostBlock::height(self)
    }

    fn timestamp(&self) -> Timestamp {
        HostBlock::timestamp(self)
    }
}
