//! Host chain types and methods, used by context mock.

use crate::{
	core::ics24_host::identifier::ChainId,
	mock::{client_state::AnyConsensusState, header::MockHeader},
	prelude::*,
	timestamp::Timestamp,
	Height,
};
use core::fmt::Debug;

/// Defines the different types of host chains that a mock context can emulate.
/// The variants are as follows:
/// - `Mock` defines that the context history consists of `MockHeader` blocks.
/// - `SyntheticTendermint`: the context has synthetically-generated Tendermint (light) blocks.
/// See also the `HostBlock` enum to get more insights into the underlying block type.
#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum MockHostType {
	Mock,
}

impl Default for MockHostType {
	fn default() -> Self {
		MockHostType::Mock
	}
}

/// Depending on `HostType` (the type of host chain underlying a context mock), this enum defines
/// the type of blocks composing the history of the host chain.
#[derive(Clone, Debug)]
pub enum MockHostBlock {
	Mock(MockHeader),
}

pub trait HostBlock {
	type HostType: Debug + Default + Copy;

	fn height(&self) -> Height;
	fn timestamp(&self) -> Timestamp;
	fn generate_block(
		chain_id: ChainId,
		chain_type: Self::HostType,
		height: u64,
		timestamp: Timestamp,
	) -> Self;
}

impl HostBlock for MockHostBlock {
	type HostType = MockHostType;

	/// Returns the height of a block.
	fn height(&self) -> Height {
		match self {
			MockHostBlock::Mock(header) => header.height(),
		}
	}

	/// Returns the timestamp of a block.
	fn timestamp(&self) -> Timestamp {
		match self {
			MockHostBlock::Mock(header) => header.timestamp,
		}
	}

	/// Generates a new block at `height` for the given chain identifier and chain type.
	fn generate_block(
		chain_id: ChainId,
		chain_type: Self::HostType,
		height: u64,
		timestamp: Timestamp,
	) -> MockHostBlock {
		match chain_type {
			MockHostType::Mock => MockHostBlock::Mock(MockHeader {
				height: Height::new(chain_id.version(), height),
				timestamp,
			}),
		}
	}
}

impl From<MockHostBlock> for AnyConsensusState {
	fn from(any_block: MockHostBlock) -> Self {
		match any_block {
			MockHostBlock::Mock(mock_header) => mock_header.into(),
		}
	}
}

// impl From<MockHostBlock> for AnyClientMessage {
// 	fn from(any_block: MockHostBlock) -> Self {
// 		match any_block {
// 			MockHostBlock::Mock(mock_header) => mock_header.into(),
// 		}
// 	}
// }
