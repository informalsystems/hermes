use crate::prelude::*;
use core::{
	convert::{TryFrom, TryInto},
	fmt::{Debug, Display},
	time::Duration,
};

use ibc_proto::{google::protobuf::Any, ibc::core::connection::v1};
use tendermint_proto::Protobuf;

use crate::core::ics02_client;
use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenTry as RawMsgConnectionOpenTry;

use crate::{
	core::{
		ics02_client::context::ClientKeeper,
		ics03_connection::{connection::Counterparty, error::Error, version::Version},
		ics23_commitment::commitment::CommitmentProofBytes,
		ics24_host::identifier::ClientId,
	},
	proofs::{ConsensusProof, Proofs},
	signer::Signer,
	tx_msg::Msg,
	Height,
};

pub const TYPE_URL: &str = "/ibc.core.connection.v1.MsgConnectionOpenTry";

///
/// Message definition `MsgConnectionOpenTry`  (i.e., `ConnOpenTry` datagram).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MsgConnectionOpenTry<C: ClientKeeper + Clone + Debug + PartialEq + Eq> {
	pub client_id: ClientId,
	pub client_state: Option<C::AnyClientState>,
	pub counterparty: Counterparty,
	pub counterparty_versions: Vec<Version>,
	pub proofs: Proofs,
	pub delay_period: Duration,
	pub signer: Signer,
}

impl<C> MsgConnectionOpenTry<C>
where
	C: ClientKeeper + Clone + Debug + PartialEq + Eq,
{
	/// Getter for accessing the `consensus_height` field from this message. Returns the special
	/// value `0` if this field is not set.
	pub fn consensus_height(&self) -> Height {
		match self.proofs.consensus_proof() {
			None => Height::zero(),
			Some(p) => p.height(),
		}
	}
}

impl<C> Msg for MsgConnectionOpenTry<C>
where
	C: ClientKeeper + Clone + Debug + PartialEq + Eq,
	Any: From<C::AnyClientState>,
{
	type ValidationError = Error;
	type Raw = RawMsgConnectionOpenTry;

	fn route(&self) -> String {
		crate::keys::ROUTER_KEY.to_string()
	}

	fn type_url(&self) -> String {
		TYPE_URL.to_string()
	}
}

impl<C> Protobuf<RawMsgConnectionOpenTry> for MsgConnectionOpenTry<C>
where
	C: ClientKeeper + Clone + Debug + PartialEq + Eq,
	Any: From<C::AnyClientState>,
	MsgConnectionOpenTry<C>: TryFrom<v1::MsgConnectionOpenTry>,
	<MsgConnectionOpenTry<C> as TryFrom<v1::MsgConnectionOpenTry>>::Error: Display,
{
}

impl<C> TryFrom<RawMsgConnectionOpenTry> for MsgConnectionOpenTry<C>
where
	C: ClientKeeper + Clone + Debug + PartialEq + Eq,
	C::AnyClientState: TryFrom<Any, Error = ics02_client::error::Error>,
{
	type Error = Error;

	fn try_from(msg: RawMsgConnectionOpenTry) -> Result<Self, Self::Error> {
		let consensus_proof_obj = {
			let proof_bytes: Option<CommitmentProofBytes> = msg.proof_consensus.try_into().ok();
			let consensus_height = msg
				.consensus_height
				.map(|height| Height::new(height.revision_number, height.revision_height));
			if proof_bytes.is_some() && consensus_height.is_some() {
				Some(
					ConsensusProof::new(proof_bytes.unwrap(), consensus_height.unwrap())
						.map_err(Error::invalid_proof)?,
				)
			} else {
				None
			}
		};

		let proof_height = msg.proof_height.ok_or_else(Error::missing_proof_height)?.into();

		let client_proof =
			CommitmentProofBytes::try_from(msg.proof_client).map_err(Error::invalid_proof)?;

		let counterparty_versions = msg
			.counterparty_versions
			.into_iter()
			.map(Version::try_from)
			.collect::<Result<Vec<_>, _>>()?;

		if counterparty_versions.is_empty() {
			return Err(Error::empty_versions())
		}

		Ok(Self {
			client_id: msg.client_id.parse().map_err(Error::invalid_identifier)?,
			client_state: msg
				.client_state
				.map(C::AnyClientState::try_from)
				.transpose()
				.map_err(Error::ics02_client)?,
			counterparty: msg.counterparty.ok_or_else(Error::missing_counterparty)?.try_into()?,
			counterparty_versions,
			proofs: Proofs::new(
				msg.proof_init.try_into().map_err(Error::invalid_proof)?,
				Some(client_proof),
				consensus_proof_obj,
				None,
				proof_height,
			)
			.map_err(Error::invalid_proof)?,
			delay_period: Duration::from_nanos(msg.delay_period),
			signer: msg.signer.parse().map_err(Error::signer)?,
		})
	}
}

impl<C> From<MsgConnectionOpenTry<C>> for RawMsgConnectionOpenTry
where
	C: ClientKeeper + Clone + Debug + PartialEq + Eq,
	Any: From<C::AnyClientState>,
{
	fn from(ics_msg: MsgConnectionOpenTry<C>) -> Self {
		RawMsgConnectionOpenTry {
			client_id: ics_msg.client_id.as_str().to_string(),
			client_state: ics_msg.client_state.map_or_else(|| None, |v| Some(v.into())),
			counterparty: Some(ics_msg.counterparty.into()),
			delay_period: ics_msg.delay_period.as_nanos() as u64,
			counterparty_versions: ics_msg
				.counterparty_versions
				.iter()
				.map(|v| v.clone().into())
				.collect(),
			proof_height: Some(ics_msg.proofs.height().into()),
			proof_init: ics_msg.proofs.object_proof().clone().into(),
			proof_client: ics_msg.proofs.client_proof().clone().map_or_else(Vec::new, |v| v.into()),
			proof_consensus: ics_msg
				.proofs
				.consensus_proof()
				.map_or_else(Vec::new, |v| v.proof().clone().into()),
			consensus_height: ics_msg
				.proofs
				.consensus_proof()
				.map_or_else(|| None, |h| Some(h.height().into())),
			signer: ics_msg.signer.to_string(),
			..Default::default()
		}
	}
}

#[cfg(test)]
pub mod test_util {
	use crate::{
		core::{
			ics02_client::context::ClientKeeper,
			ics03_connection::{
				msgs::{
					conn_open_try::MsgConnectionOpenTry, test_util::get_dummy_raw_counterparty,
				},
				version::get_compatible_versions,
			},
			ics24_host::identifier::ClientId,
		},
		mock::{
			client_state::{AnyClientState, MockClientState},
			header::MockHeader,
		},
		prelude::*,
		test_utils::{get_dummy_bech32_account, get_dummy_proof},
	};
	use core::fmt::Debug;
	use ibc_proto::ibc::core::{
		client::v1::Height, connection::v1::MsgConnectionOpenTry as RawMsgConnectionOpenTry,
	};

	/// Testing-specific helper methods.
	impl<C> MsgConnectionOpenTry<C>
	where
		C: ClientKeeper + Clone + Debug + Eq,
	{
		/// Setter for `client_id`.
		pub fn with_client_id(self, client_id: ClientId) -> MsgConnectionOpenTry<C> {
			MsgConnectionOpenTry { client_id, ..self }
		}
	}

	/// Returns a dummy `RawMsgConnectionOpenTry` with parametrized heights. The parameter
	/// `proof_height` represents the height, on the source chain, at which this chain produced the
	/// proof. Parameter `consensus_height` represents the height of destination chain which a
	/// client on the source chain stores.
	pub fn get_dummy_raw_msg_conn_open_try(
		proof_height: u64,
		consensus_height: u64,
	) -> RawMsgConnectionOpenTry {
		RawMsgConnectionOpenTry {
			client_id: ClientId::default().to_string(),
			client_state: Some(
				AnyClientState::Mock(MockClientState::new(MockHeader::default())).into(),
			),
			counterparty: Some(get_dummy_raw_counterparty()),
			delay_period: 0,
			counterparty_versions: get_compatible_versions()
				.iter()
				.map(|v| v.clone().into())
				.collect(),
			proof_init: get_dummy_proof(),
			proof_height: Some(Height { revision_number: 0, revision_height: proof_height }),
			proof_consensus: get_dummy_proof(),
			consensus_height: Some(Height {
				revision_number: 0,
				revision_height: consensus_height,
			}),
			proof_client: get_dummy_proof(),
			signer: get_dummy_bech32_account(),
			..Default::default()
		}
	}
}

#[cfg(test)]
mod tests {
	use crate::prelude::*;

	use test_log::test;

	use ibc_proto::ibc::core::{
		client::v1::Height,
		connection::v1::{
			Counterparty as RawCounterparty, MsgConnectionOpenTry as RawMsgConnectionOpenTry,
		},
	};

	use crate::{
		core::ics03_connection::msgs::{
			conn_open_try::{test_util::get_dummy_raw_msg_conn_open_try, MsgConnectionOpenTry},
			test_util::get_dummy_raw_counterparty,
		},
		mock::context::{MockClientTypes, MockContext},
	};

	#[test]
	fn parse_connection_open_try_msg() {
		#[derive(Clone, Debug, PartialEq)]
		struct Test {
			name: String,
			raw: RawMsgConnectionOpenTry,
			want_pass: bool,
		}

		let default_try_msg = get_dummy_raw_msg_conn_open_try(10, 34);

		let tests: Vec<Test> = vec![
			Test {
				name: "Good parameters".to_string(),
				raw: default_try_msg.clone(),
				want_pass: true,
			},
			Test {
				name: "Bad client id, name too short".to_string(),
				raw: RawMsgConnectionOpenTry {
					client_id: "client".to_string(),
					..default_try_msg.clone()
				},
				want_pass: false,
			},
			Test {
				name: "Bad destination connection id, name too long".to_string(),
				raw: RawMsgConnectionOpenTry {
					counterparty: Some(RawCounterparty {
						connection_id:
							"abcdasdfasdfsdfasfdwefwfsdfsfsfasfwewvxcvdvwgadvaadsefghijklmnopqrstu"
								.to_string(),
						..get_dummy_raw_counterparty()
					}),
					..default_try_msg.clone()
				},
				want_pass: false,
			},
			Test {
				name: "Correct destination client id with lower/upper case and special chars"
					.to_string(),
				raw: RawMsgConnectionOpenTry {
					counterparty: Some(RawCounterparty {
						client_id: "ClientId_".to_string(),
						..get_dummy_raw_counterparty()
					}),
					..default_try_msg.clone()
				},
				want_pass: true,
			},
			Test {
				name: "Bad counterparty versions, empty versions vec".to_string(),
				raw: RawMsgConnectionOpenTry {
					counterparty_versions: Vec::new(),
					..default_try_msg.clone()
				},
				want_pass: false,
			},
			Test {
				name: "Bad counterparty versions, empty version string".to_string(),
				raw: RawMsgConnectionOpenTry {
					counterparty_versions: Vec::new(),
					..default_try_msg.clone()
				},
				want_pass: false,
			},
			Test {
				name: "Bad proof height, height is 0".to_string(),
				raw: RawMsgConnectionOpenTry {
					proof_height: Some(Height { revision_number: 1, revision_height: 0 }),
					..default_try_msg.clone()
				},
				want_pass: false,
			},
			Test {
				name: "Bad consensus height, height is 0".to_string(),
				raw: RawMsgConnectionOpenTry {
					proof_height: Some(Height { revision_number: 1, revision_height: 0 }),
					..default_try_msg.clone()
				},
				want_pass: false,
			},
			Test {
				name: "Empty proof".to_string(),
				raw: RawMsgConnectionOpenTry { proof_init: b"".to_vec(), ..default_try_msg },
				want_pass: false,
			},
		]
		.into_iter()
		.collect();

		for test in tests {
			let msg =
				MsgConnectionOpenTry::<MockContext<MockClientTypes>>::try_from(test.raw.clone());

			assert_eq!(
				test.want_pass,
				msg.is_ok(),
				"MsgConnOpenTry::new failed for test {}, \nmsg {:?} with error {:?}",
				test.name,
				test.raw,
				msg.err(),
			);
		}
	}

	#[test]
	fn to_and_from() {
		let raw = get_dummy_raw_msg_conn_open_try(10, 34);
		let msg =
			MsgConnectionOpenTry::<MockContext<MockClientTypes>>::try_from(raw.clone()).unwrap();
		let raw_back = RawMsgConnectionOpenTry::from(msg.clone());
		let msg_back = MsgConnectionOpenTry::try_from(raw_back.clone()).unwrap();
		assert_eq!(raw, raw_back);
		assert_eq!(msg, msg_back);
	}
}
