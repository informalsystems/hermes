use crate::ics02_client::client_def::{AnyConsensusState, AnyHeader};
use crate::ics07_tendermint::consensus_state::ConsensusState as TMConsensusState;
use crate::ics07_tendermint::header::Header as TMHeader;
use crate::ics24_host::identifier::ChainId;
use crate::mock_client::header::MockHeader;
use crate::Height;

use tendermint::chain::Id as TMChainId;
use tendermint_testgen::light_block::TMLightBlock;
use tendermint_testgen::{Generator, LightBlock};

use std::convert::TryFrom;

/// Defines the different types of host chains that a mock context can emulate, as follows:
/// - `Mock` defines that the context history comprises `MockHeader` blocks.
/// - `SyntheticTendermint`: the context has synthetically-generated Tendermint (light) blocks.
#[derive(Clone, Debug, Copy)]
pub enum HostType {
    Mock,
    SyntheticTendermint,
}

/// Depending on `HostType` (the type of host chain underlying a context mock), this enum defines
/// the blocks that compose the history of the host chain.
#[derive(Clone, Debug)]
pub enum HostBlock {
    Mock(MockHeader),
    SyntheticTendermint(Box<TMLightBlock>),
}

impl HostBlock {
    pub fn height(&self) -> Height {
        match self {
            HostBlock::Mock(header) => header.height(),
            HostBlock::SyntheticTendermint(light_block) => Height::new(
                ChainId::chain_version(light_block.signed_header.header.chain_id.to_string()),
                light_block.signed_header.header.height.value(),
            ),
        }
    }

    pub fn generate_block(
        chain_id: ChainId,
        chain_type: HostType,
        target_version_height: u64,
    ) -> HostBlock {
        match chain_type {
            HostType::Mock => HostBlock::Mock(MockHeader(Height::new(
                ChainId::chain_version(chain_id.to_string()),
                target_version_height,
            ))),
            HostType::SyntheticTendermint => {
                let mut block = LightBlock::new_default(target_version_height)
                    .generate()
                    .unwrap();
                block.signed_header.header.chain_id =
                    TMChainId::try_from(chain_id.to_string()).unwrap();
                HostBlock::SyntheticTendermint(Box::new(block))
            }
        }
    }
}

impl From<HostBlock> for AnyConsensusState {
    fn from(any_block: HostBlock) -> Self {
        match any_block {
            HostBlock::Mock(mock_header) => mock_header.into(),
            HostBlock::SyntheticTendermint(light_block) => {
                // Conversion between TMLightBlock and AnyConsensusState
                let sh = light_block.signed_header;
                let cs = TMConsensusState::from(sh);
                AnyConsensusState::Tendermint(cs)
            }
        }
    }
}

impl From<HostBlock> for AnyHeader {
    fn from(any_block: HostBlock) -> Self {
        match any_block {
            HostBlock::Mock(mock_header) => mock_header.into(),
            HostBlock::SyntheticTendermint(light_block_box) => {
                // Conversion between TMLightBlock and AnyHeader
                AnyHeader::Tendermint((*light_block_box).into())
            }
        }
    }
}

impl From<TMLightBlock> for TMHeader {
    fn from(light_block: TMLightBlock) -> Self {
        // TODO: This conversion is incorrect for `trusted_height` and `trusted_validator_set`.
        TMHeader {
            signed_header: light_block.signed_header,
            validator_set: light_block.validators,
            trusted_height: Default::default(),
            trusted_validator_set: light_block.next_validators,
        }
    }
}
