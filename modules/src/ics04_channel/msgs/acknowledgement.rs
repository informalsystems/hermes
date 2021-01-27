use std::convert::{TryFrom, TryInto};

use tendermint::account::Id as AccountId;
use tendermint_proto::Protobuf;

use ibc_proto::ibc::core::channel::v1::MsgAcknowledgement as RawMsgAcknowledgement;

use crate::address::{account_to_string, string_to_account};
use crate::ics04_channel::error::{Error, Kind};
use crate::ics04_channel::packet::Packet;
use crate::{proofs::Proofs, tx_msg::Msg};

pub const TYPE_URL: &str = "/ibc.core.channel.v1.MsgAcknowledgement";

///
/// Message definition for packet acknowledgements.
///
#[derive(Clone, Debug, PartialEq)]
pub struct MsgAcknowledgement {
    pub packet: Packet,
    acknowledgement: Vec<u8>,
    proofs: Proofs,
    signer: AccountId,
}

impl MsgAcknowledgement {
    pub fn new(
        packet: Packet,
        acknowledgement: Vec<u8>,
        proofs: Proofs,
        signer: AccountId,
    ) -> Result<MsgAcknowledgement, Error> {
        Ok(Self {
            packet,
            acknowledgement,
            proofs,
            signer,
        })
    }
}

impl Msg for MsgAcknowledgement {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

impl Protobuf<RawMsgAcknowledgement> for MsgAcknowledgement {}

impl TryFrom<RawMsgAcknowledgement> for MsgAcknowledgement {
    type Error = anomaly::Error<Kind>;

    fn try_from(raw_msg: RawMsgAcknowledgement) -> Result<Self, Self::Error> {
        let signer =
            string_to_account(raw_msg.signer).map_err(|e| Kind::InvalidSigner.context(e))?;

        let proofs = Proofs::new(
            raw_msg.proof_acked.into(),
            None,
            None,
            None,
            raw_msg
                .proof_height
                .ok_or(Kind::MissingHeight)?
                .try_into()
                .map_err(|e| Kind::InvalidProof.context(e))?,
        )
        .map_err(|e| Kind::InvalidProof.context(e))?;

        Ok(MsgAcknowledgement {
            packet: raw_msg
                .packet
                .ok_or(Kind::MissingPacket)?
                .try_into()
                .map_err(|e| Kind::InvalidPacket.context(e))?,
            acknowledgement: raw_msg.acknowledgement,
            signer,
            proofs,
        })
    }
}

impl From<MsgAcknowledgement> for RawMsgAcknowledgement {
    fn from(domain_msg: MsgAcknowledgement) -> Self {
        RawMsgAcknowledgement {
            packet: Some(domain_msg.packet.into()),
            acknowledgement: domain_msg.acknowledgement,
            signer: account_to_string(domain_msg.signer).unwrap(),
            proof_height: Some(domain_msg.proofs.height().into()),
            proof_acked: domain_msg.proofs.object_proof().clone().into(),
        }
    }
}

#[cfg(test)]
mod test_util {
    use ibc_proto::ibc::core::channel::v1::MsgAcknowledgement as RawMsgAcknowledgement;
    use ibc_proto::ibc::core::client::v1::Height as RawHeight;

    use crate::ics04_channel::packet::test_utils::get_dummy_raw_packet;
    use crate::test_utils::{get_dummy_bech32_account, get_dummy_proof};

    /// Returns a dummy `RawMsgAcknowledgement`, for testing only!
    /// The `height` parametrizes both the proof height as well as the timeout height.
    pub fn get_dummy_raw_msg_acknowledgement(height: u64) -> RawMsgAcknowledgement {
        RawMsgAcknowledgement {
            packet: Some(get_dummy_raw_packet(height)),
            acknowledgement: get_dummy_proof(),
            proof_acked: get_dummy_proof(),
            proof_height: Some(RawHeight {
                revision_number: 0,
                revision_height: height,
            }),
            signer: get_dummy_bech32_account(),
        }
    }
}

#[cfg(test)]
mod test {
    use std::convert::TryInto;

    use ibc_proto::ibc::core::channel::v1::MsgAcknowledgement as RawMsgAcknowledgement;

    use crate::ics04_channel::error::Error;
    use crate::ics04_channel::msgs::acknowledgement::test_util::get_dummy_raw_msg_acknowledgement;
    use crate::ics04_channel::msgs::acknowledgement::MsgAcknowledgement;

    #[test]
    fn msg_acknowledgment_try_from_raw() {
        struct Test {
            name: String,
            raw: RawMsgAcknowledgement,
            want_pass: bool,
        }

        let height = 50;
        let default_raw_msg = get_dummy_raw_msg_acknowledgement(height);

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                raw: default_raw_msg.clone(),
                want_pass: true,
            },
            Test {
                name: "Missing packet".to_string(),
                raw: RawMsgAcknowledgement {
                    packet: None,
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Missing proof height".to_string(),
                raw: RawMsgAcknowledgement {
                    proof_height: None,
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Missing signer".to_string(),
                raw: RawMsgAcknowledgement {
                    signer: "".to_string(),
                    ..default_raw_msg.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Empty proof acked".to_string(),
                raw: RawMsgAcknowledgement {
                    proof_acked: vec![],
                    ..default_raw_msg
                },
                want_pass: false,
            },
        ];

        for test in tests {
            let res_msg: Result<MsgAcknowledgement, Error> = test.raw.clone().try_into();

            assert_eq!(
                res_msg.is_ok(),
                test.want_pass,
                "MsgAcknowledgement::try_from failed for test {} \nraw message: {:?} with error: {:?}",
                test.name,
                test.raw,
                res_msg.err()
            );
        }
    }
}
