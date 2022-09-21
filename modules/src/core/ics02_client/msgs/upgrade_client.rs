//! Definition of domain type msg `MsgUpgradeAnyClient`.

use crate::prelude::*;
use core::fmt::Display;

use core::str::FromStr;
use ibc_proto::google::protobuf::Any;
use tendermint_proto::Protobuf;

use ibc_proto::ibc::core::client::v1::{MsgUpgradeClient as RawMsgUpgradeClient, MsgUpgradeClient};

use crate::{
	core::{
		ics02_client::{context::ClientKeeper, error::Error},
		ics24_host::identifier::ClientId,
	},
	signer::Signer,
	tx_msg::Msg,
};

pub(crate) const TYPE_URL: &str = "/ibc.core.client.v1.MsgUpgradeClient";

/// A type of message that triggers the upgrade of an on-chain (IBC) client.
#[derive(Clone, Debug, PartialEq)]
pub struct MsgUpgradeAnyClient<C: ClientKeeper> {
	pub client_id: ClientId,
	pub client_state: C::AnyClientState,
	pub consensus_state: C::AnyConsensusState,
	pub proof_upgrade_client: Vec<u8>,
	pub proof_upgrade_consensus_state: Vec<u8>,
	pub signer: Signer,
}
impl<C: ClientKeeper> MsgUpgradeAnyClient<C> {
	pub fn new(
		client_id: ClientId,
		client_state: C::AnyClientState,
		consensus_state: C::AnyConsensusState,
		proof_upgrade_client: Vec<u8>,
		proof_upgrade_consensus_state: Vec<u8>,
		signer: Signer,
	) -> Self {
		MsgUpgradeAnyClient {
			client_id,
			client_state,
			consensus_state,
			proof_upgrade_client,
			proof_upgrade_consensus_state,
			signer,
		}
	}
}

impl<C> Msg for MsgUpgradeAnyClient<C>
where
	C: ClientKeeper + Clone,
	Any: From<C::AnyClientState>,
	Any: From<C::AnyConsensusState>,
{
	type ValidationError = crate::core::ics24_host::error::ValidationError;
	type Raw = RawMsgUpgradeClient;

	fn route(&self) -> String {
		crate::keys::ROUTER_KEY.to_string()
	}

	fn type_url(&self) -> String {
		TYPE_URL.to_string()
	}
}

impl<C> Protobuf<RawMsgUpgradeClient> for MsgUpgradeAnyClient<C>
where
	C: ClientKeeper + Clone,
	Any: From<C::AnyClientState>,
	Any: From<C::AnyConsensusState>,
	MsgUpgradeAnyClient<C>: TryFrom<MsgUpgradeClient>,
	<MsgUpgradeAnyClient<C> as TryFrom<MsgUpgradeClient>>::Error: Display,
{
}

impl<C> From<MsgUpgradeAnyClient<C>> for RawMsgUpgradeClient
where
	C: ClientKeeper,
	Any: From<C::AnyClientState>,
	Any: From<C::AnyConsensusState>,
{
	fn from(dm_msg: MsgUpgradeAnyClient<C>) -> RawMsgUpgradeClient {
		RawMsgUpgradeClient {
			client_id: dm_msg.client_id.to_string(),
			client_state: Some(dm_msg.client_state.into()),
			consensus_state: Some(dm_msg.consensus_state.into()),
			proof_upgrade_client: dm_msg.proof_upgrade_client,
			proof_upgrade_consensus_state: dm_msg.proof_upgrade_consensus_state,
			signer: dm_msg.signer.to_string(),
		}
	}
}

impl<C> TryFrom<RawMsgUpgradeClient> for MsgUpgradeAnyClient<C>
where
	C: ClientKeeper,
	C::AnyClientState: TryFrom<Any>,
	C::AnyConsensusState: TryFrom<Any>,
	Error: From<<C::AnyClientState as TryFrom<Any>>::Error>,
	Error: From<<C::AnyConsensusState as TryFrom<Any>>::Error>,
{
	type Error = Error;

	fn try_from(proto_msg: RawMsgUpgradeClient) -> Result<Self, Self::Error> {
		let raw_client_state =
			proto_msg.client_state.ok_or_else(Error::missing_raw_client_state)?;

		let raw_consensus_state =
			proto_msg.consensus_state.ok_or_else(Error::missing_raw_client_state)?;

		Ok(MsgUpgradeAnyClient {
			client_id: ClientId::from_str(&proto_msg.client_id)
				.map_err(Error::invalid_client_identifier)?,
			client_state: C::AnyClientState::try_from(raw_client_state)?,
			consensus_state: C::AnyConsensusState::try_from(raw_consensus_state)?,
			proof_upgrade_client: proto_msg.proof_upgrade_client,
			proof_upgrade_consensus_state: proto_msg.proof_upgrade_consensus_state,
			signer: Signer::from_str(proto_msg.signer.as_str()).map_err(Error::signer)?,
		})
	}
}

#[cfg(test)]
pub mod test_util {
	use ibc_proto::ibc::core::client::v1::MsgUpgradeClient as RawMsgUpgradeClient;

	use crate::{
		core::{ics02_client::height::Height, ics24_host::identifier::ClientId},
		mock::{
			client_state::{
				AnyClientState, AnyConsensusState, MockClientState, MockConsensusState,
			},
			context::{MockClientTypes, MockContext},
			header::MockHeader,
		},
		test_utils::{get_dummy_bech32_account, get_dummy_proof},
	};

	use super::MsgUpgradeAnyClient;

	/// Extends the implementation with additional helper methods.
	impl MsgUpgradeAnyClient<MockContext<MockClientTypes>> {
		/// Setter for `client_id`. Amenable to chaining, since it consumes the input message.
		pub fn with_client_id(self, client_id: ClientId) -> Self {
			MsgUpgradeAnyClient { client_id, ..self }
		}
	}

	/// Returns a dummy `RawMsgUpgradeClient`, for testing only!
	pub fn get_dummy_raw_msg_upgrade_client(height: Height) -> RawMsgUpgradeClient {
		RawMsgUpgradeClient {
			client_id: "tendermint".parse().unwrap(),
			client_state: Some(
				AnyClientState::Mock(MockClientState::new(MockHeader::new(height).into())).into(),
			),
			consensus_state: Some(
				AnyConsensusState::Mock(MockConsensusState::new(MockHeader::new(height))).into(),
			),
			proof_upgrade_client: get_dummy_proof(),
			proof_upgrade_consensus_state: get_dummy_proof(),
			signer: get_dummy_bech32_account(),
		}
	}
}

#[cfg(test)]
mod tests {

	use alloc::vec::Vec;
	use ibc_proto::ibc::core::client::v1::MsgUpgradeClient as RawMsgUpgradeClient;

	use crate::{
		core::{
			ics02_client::{height::Height, msgs::upgrade_client::MsgUpgradeAnyClient},
			ics23_commitment::commitment::test_util::get_dummy_merkle_proof,
			ics24_host::identifier::ClientId,
		},
		mock::{
			client_state::{
				AnyClientState, AnyConsensusState, MockClientState, MockConsensusState,
			},
			context::{MockClientTypes, MockContext},
			header::MockHeader,
		},
		test_utils::get_dummy_account_id,
	};

	#[test]
	fn msg_upgrade_client_serialization() {
		let client_id: ClientId = "tendermint".parse().unwrap();
		let signer = get_dummy_account_id();

		let height = Height::new(1, 1);

		let client_state =
			AnyClientState::Mock(MockClientState::new(MockHeader::new(height).into()));
		let consensus_state =
			AnyConsensusState::Mock(MockConsensusState::new(MockHeader::new(height)));

		let proof = get_dummy_merkle_proof();
		let mut proof_buf = Vec::new();
		prost::Message::encode(&proof, &mut proof_buf).unwrap();
		let msg = MsgUpgradeAnyClient::<MockContext<MockClientTypes>>::new(
			client_id,
			client_state,
			consensus_state,
			proof_buf.clone(),
			proof_buf,
			signer,
		);
		let raw: RawMsgUpgradeClient = RawMsgUpgradeClient::from(msg.clone());
		let msg_back = MsgUpgradeAnyClient::try_from(raw.clone()).unwrap();
		let raw_back: RawMsgUpgradeClient = RawMsgUpgradeClient::from(msg_back.clone());
		assert_eq!(msg, msg_back);
		assert_eq!(raw, raw_back);
	}
}
