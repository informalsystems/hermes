#![allow(clippy::too_many_arguments)]
use super::channel::{ChannelEnd, Counterparty, Order};

use crate::ics03_connection::connection::validate_version;
use crate::ics04_channel::error::{Error, Kind};
use crate::ics04_channel::packet::Packet;
use crate::ics23_commitment::commitment::CommitmentProof;
use crate::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use crate::{proofs::Proofs, tx_msg::Msg, Height};
use serde_derive::{Deserialize, Serialize};
use std::str::FromStr;
use tendermint::account::Id as AccountId;

pub const TYPE_MSG_CHANNEL_OPEN_INIT: &str = "channel_open_init";

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgChannelOpenInit {
    port_id: PortId,
    channel_id: ChannelId,
    channel: ChannelEnd,
    signer: AccountId,
}

impl MsgChannelOpenInit {
    pub fn new(
        port_id: String,
        channel_id: String,
        version: String,
        order: i32,
        connection_hops: Vec<String>,
        counterparty_port_id: String,
        counterparty_channel_id: String,
        signer: AccountId,
    ) -> Result<MsgChannelOpenInit, Error> {
        let connection_hops: Result<Vec<_>, _> = connection_hops
            .into_iter()
            .map(|s| ConnectionId::from_str(s.as_str()))
            .collect();

        Ok(Self {
            port_id: port_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel_id: channel_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel: ChannelEnd::new(
                Order::from_i32(order)?,
                Counterparty::new(counterparty_port_id, counterparty_channel_id)
                    .map_err(|e| Kind::IdentifierError.context(e))?,
                connection_hops.map_err(|e| Kind::IdentifierError.context(e))?,
                version,
            ),
            signer,
        })
    }
}

impl Msg for MsgChannelOpenInit {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_CHANNEL_OPEN_INIT.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        self.channel.validate_basic()
    }

    fn get_sign_bytes(&self) -> Vec<u8> {
        todo!()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

pub const TYPE_MSG_CHANNEL_OPEN_TRY: &str = "channel_open_try";

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgChannelOpenTry {
    port_id: PortId,
    channel_id: ChannelId,
    channel: ChannelEnd,
    counterparty_version: String,
    proofs: Proofs,
    signer: AccountId,
}

impl MsgChannelOpenTry {
    pub fn new(
        port_id: String,
        channel_id: String,
        channel_version: String,
        order: i32,
        connection_hops: Vec<String>,
        counterparty_port_id: String,
        counterparty_channel_id: String,
        counterparty_version: String,
        proof_init: CommitmentProof,
        proofs_height: Height,
        signer: AccountId,
    ) -> Result<MsgChannelOpenTry, Error> {
        let connection_hops: Result<Vec<_>, _> = connection_hops
            .into_iter()
            .map(|s| ConnectionId::from_str(s.as_str()))
            .collect();

        let version =
            validate_version(channel_version).map_err(|e| Kind::InvalidVersion.context(e))?;

        Ok(Self {
            port_id: port_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel_id: channel_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel: ChannelEnd::new(
                Order::from_i32(order)?,
                Counterparty::new(counterparty_port_id, counterparty_channel_id)
                    .map_err(|e| Kind::IdentifierError.context(e))?,
                connection_hops.map_err(|e| Kind::IdentifierError.context(e))?,
                version,
            ),
            counterparty_version: validate_version(counterparty_version)
                .map_err(|e| Kind::InvalidVersion.context(e))?,
            proofs: Proofs::new(proof_init, None, None, proofs_height)
                .map_err(|e| Kind::InvalidProof.context(e))?,
            signer,
        })
    }
}

impl Msg for MsgChannelOpenTry {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_CHANNEL_OPEN_TRY.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        self.channel.validate_basic()
    }

    fn get_sign_bytes(&self) -> Vec<u8> {
        todo!()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

pub const TYPE_MSG_CHANNEL_OPEN_ACK: &str = "channel_open_ack";

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgChannelOpenAck {
    port_id: PortId,
    channel_id: ChannelId,
    counterparty_version: String,
    proofs: Proofs,
    signer: AccountId,
}

impl MsgChannelOpenAck {
    pub fn new(
        port_id: String,
        channel_id: String,
        counterparty_version: String,
        proof_try: CommitmentProof,
        proofs_height: Height,
        signer: AccountId,
    ) -> Result<MsgChannelOpenAck, Error> {
        Ok(Self {
            port_id: port_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel_id: channel_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            counterparty_version: validate_version(counterparty_version)
                .map_err(|e| Kind::InvalidVersion.context(e))?,
            proofs: Proofs::new(proof_try, None, None, proofs_height)
                .map_err(|e| Kind::InvalidProof.context(e))?,
            signer,
        })
    }
}

impl Msg for MsgChannelOpenAck {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_CHANNEL_OPEN_ACK.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        // Nothing to validate
        // All the validation is performed on creation
        Ok(())
    }

    fn get_sign_bytes(&self) -> Vec<u8> {
        todo!()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

pub const TYPE_MSG_CHANNEL_OPEN_CONFIRM: &str = "channel_open_confirm";

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgChannelOpenConfirm {
    port_id: PortId,
    channel_id: ChannelId,
    proofs: Proofs,
    signer: AccountId,
}

impl MsgChannelOpenConfirm {
    pub fn new(
        port_id: String,
        channel_id: String,
        proof_ack: CommitmentProof,
        proofs_height: Height,
        signer: AccountId,
    ) -> Result<MsgChannelOpenConfirm, Error> {
        Ok(Self {
            port_id: port_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel_id: channel_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            proofs: Proofs::new(proof_ack, None, None, proofs_height)
                .map_err(|e| Kind::InvalidProof.context(e))?,
            signer,
        })
    }
}

impl Msg for MsgChannelOpenConfirm {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_CHANNEL_OPEN_CONFIRM.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        // Nothing to validate
        // All the validation is performed on creation
        Ok(())
    }

    fn get_sign_bytes(&self) -> Vec<u8> {
        todo!()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

pub const TYPE_MSG_CHANNEL_CLOSE_INIT: &str = "channel_close_init";

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgChannelCloseInit {
    port_id: PortId,
    channel_id: ChannelId,
    signer: AccountId,
}

impl MsgChannelCloseInit {
    pub fn new(
        port_id: String,
        channel_id: String,
        signer: AccountId,
    ) -> Result<MsgChannelCloseInit, Error> {
        Ok(Self {
            port_id: port_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel_id: channel_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            signer,
        })
    }
}

impl Msg for MsgChannelCloseInit {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_CHANNEL_CLOSE_INIT.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        // Nothing to validate
        // All the validation is performed on creation
        Ok(())
    }

    fn get_sign_bytes(&self) -> Vec<u8> {
        todo!()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

pub const TYPE_MSG_CHANNEL_CLOSE_CONFIRM: &str = "channel_close_confirm";

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgChannelCloseConfirm {
    port_id: PortId,
    channel_id: ChannelId,
    proofs: Proofs,
    signer: AccountId,
}

impl MsgChannelCloseConfirm {
    pub fn new(
        port_id: String,
        channel_id: String,
        proof_init: CommitmentProof,
        proofs_height: Height,
        signer: AccountId,
    ) -> Result<MsgChannelCloseConfirm, Error> {
        Ok(Self {
            port_id: port_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel_id: channel_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            proofs: Proofs::new(proof_init, None, None, proofs_height)
                .map_err(|e| Kind::InvalidProof.context(e))?,
            signer,
        })
    }
}

impl Msg for MsgChannelCloseConfirm {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_CHANNEL_CLOSE_CONFIRM.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        // Nothing to validate
        // All the validation is performed on creation
        Ok(())
    }

    fn get_sign_bytes(&self) -> Vec<u8> {
        todo!()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

pub const TYPE_MSG_PACKET: &str = "ics04/opaque";

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgPacket {
    packet: Packet,
    proofs: Proofs,
    signer: AccountId,
}

impl MsgPacket {
    pub fn new(
        packet: Packet,
        proof: CommitmentProof,
        proof_height: Height,
        signer: AccountId,
    ) -> Result<MsgPacket, Error> {
        Ok(Self {
            packet: packet
                .validate()
                .map_err(|e| Kind::InvalidPacket.context(e))?,
            proofs: Proofs::new(proof, None, None, proof_height)
                .map_err(|e| Kind::InvalidProof.context(e))?,
            signer,
        })
    }

    // returns the base64-encoded bytes used for the
    // data field when signing the packet
    pub fn get_data_bytes() -> Vec<u8> {
        todo!()
    }
}

impl Msg for MsgPacket {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_PACKET.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        // Nothing to validate
        // All the validation is performed on creation
        Ok(())
    }

    fn get_sign_bytes(&self) -> Vec<u8> {
        todo!()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

pub const TYPE_MSG_TIMEOUT: &str = "ics04/timeout";

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgTimeout {
    packet: Packet,
    next_sequence_recv: Option<u64>,
    proofs: Proofs,
    signer: AccountId,
}

impl MsgTimeout {
    pub fn new(
        packet: Packet,
        next_sequence_recv: Option<u64>,
        proof: CommitmentProof,
        proof_height: Height,
        signer: AccountId,
    ) -> Result<MsgTimeout, Error> {
        Ok(Self {
            packet: packet
                .validate()
                .map_err(|e| Kind::InvalidPacket.context(e))?,
            next_sequence_recv,
            proofs: Proofs::new(proof, None, None, proof_height)
                .map_err(|e| Kind::InvalidProof.context(e))?,
            signer,
        })
    }
}

impl Msg for MsgTimeout {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_TIMEOUT.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        // Nothing to validate
        // All the validation is performed on creation
        Ok(())
    }

    fn get_sign_bytes(&self) -> Vec<u8> {
        todo!()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

pub const TYPE_MSG_ACKNOWLEDGEMENT: &str = "ics04/opaque";

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgAcknowledgement {
    packet: Packet,
    acknowledgement: Vec<u8>,
    proofs: Proofs,
    signer: AccountId,
}

impl MsgAcknowledgement {
    pub fn new(
        packet: Packet,
        acknowledgement: Vec<u8>,
        proof: CommitmentProof,
        proof_height: Height,
        signer: AccountId,
    ) -> Result<MsgAcknowledgement, Error> {
        if acknowledgement.len() > 100 {
            return Err(Kind::AcknowledgementTooLong.into());
        }

        Ok(Self {
            packet: packet
                .validate()
                .map_err(|e| Kind::InvalidPacket.context(e))?,
            acknowledgement,
            proofs: Proofs::new(proof, None, None, proof_height)
                .map_err(|e| Kind::InvalidProof.context(e))?,
            signer,
        })
    }
}

impl Msg for MsgAcknowledgement {
    type ValidationError = Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_ACKNOWLEDGEMENT.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        // Nothing to validate
        // All the validation is performed on creation
        Ok(())
    }

    fn get_sign_bytes(&self) -> Vec<u8> {
        todo!()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

#[cfg(test)]
mod tests {
    use super::MsgChannelOpenInit;
    use crate::ics03_connection::msgs::test_util::get_dummy_proof;
    use crate::ics04_channel::channel::Order;
    use crate::ics04_channel::msgs::{
        MsgChannelCloseConfirm, MsgChannelCloseInit, MsgChannelOpenAck, MsgChannelOpenConfirm,
        MsgChannelOpenTry,
    };
    use crate::ics23_commitment::commitment::CommitmentProof;
    use crate::Height;
    use std::str::FromStr;
    use tendermint::account::Id as AccountId;

    #[test]
    fn parse_channel_open_init_msg() {
        let id_hex = "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C";
        let acc = AccountId::from_str(id_hex).unwrap();

        #[derive(Clone, Debug, PartialEq)]
        struct OpenInitParams {
            port_id: String,
            channel_id: String,
            version: String,
            order: i32,
            connection_hops: Vec<String>,
            counterparty_port_id: String,
            counterparty_channel_id: String,
        }

        let default_params = OpenInitParams {
            port_id: "port".to_string(),
            channel_id: "testchannel".to_string(),
            version: "1.0".to_string(),
            order: Order::from_str("ORDERED").unwrap() as i32,
            connection_hops: vec!["connectionhop".to_string()].into_iter().collect(),
            counterparty_port_id: "destport".to_string(),
            counterparty_channel_id: "testdestchannel".to_string(),
        };

        struct Test {
            name: String,
            params: OpenInitParams,
            want_pass: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                params: default_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Correct port identifier".to_string(),
                params: OpenInitParams {
                    port_id: "p34".to_string(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Incorrect port identifier, slash (separator) prohibited".to_string(),
                params: OpenInitParams {
                    port_id: "p34/".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad channel, name too short".to_string(),
                params: OpenInitParams {
                    channel_id: "chshort".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad version".to_string(),
                params: OpenInitParams {
                    version: " . ".to_string(),
                    ..default_params.clone()
                },
                want_pass: true, // verified in validate_basic()
            },
            Test {
                name: "Bad order".to_string(),
                params: OpenInitParams {
                    order: 99,
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad connection hops (conn id too short, must be 10 chars)".to_string(),
                params: OpenInitParams {
                    connection_hops: vec!["conn124".to_string()].into_iter().collect(),
                    ..default_params
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let p = test.params.clone();

            let msg = MsgChannelOpenInit::new(
                p.port_id,
                p.channel_id,
                p.version,
                p.order,
                p.connection_hops,
                p.counterparty_port_id,
                p.counterparty_channel_id,
                acc,
            );

            assert_eq!(
                test.want_pass,
                msg.is_ok(),
                "MsgChanOpenInit::new failed for test {}, \nmsg {:?} with error {:?}",
                test.name,
                test.params.clone(),
                msg.err(),
            );
        }
    }

    #[test]
    fn parse_channel_open_try_msg() {
        let id_hex = "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C";
        let acc = AccountId::from_str(id_hex).unwrap();

        #[derive(Clone, Debug, PartialEq)]
        struct OpenTryParams {
            port_id: String,
            channel_id: String,
            channel_version: String,
            order: i32,
            connection_hops: Vec<String>,
            counterparty_port_id: String,
            counterparty_channel_id: String,
            counterparty_version: String,
            proof_init: CommitmentProof,
            proof_height: Height,
        }

        let default_params = OpenTryParams {
            port_id: "port".to_string(),
            channel_id: "testchannel".to_string(),
            channel_version: "1.0".to_string(),
            order: Order::from_str("ORDERED").unwrap() as i32,
            connection_hops: vec!["connectionhop".to_string()].into_iter().collect(),
            counterparty_port_id: "destport".to_string(),
            counterparty_channel_id: "testdestchannel".to_string(),
            counterparty_version: "1.0".to_string(),
            proof_init: get_dummy_proof().into(),
            proof_height: Height {
                version_number: 0,
                version_height: 10,
            },
        };

        struct Test {
            name: String,
            params: OpenTryParams,
            want_pass: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                params: default_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Correct port".to_string(),
                params: OpenTryParams {
                    port_id: "p34".to_string(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad port, name too short".to_string(),
                params: OpenTryParams {
                    port_id: "p".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad port, name too long".to_string(),
                params: OpenTryParams {
                    port_id: "abcdefghijasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfadgasgasdfasdfasdfasdfaklmnopqrstu".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct channel identifier".to_string(),
                params: OpenTryParams {
                    channel_id: "channelid34".to_string(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad channel, name too short".to_string(),
                params: OpenTryParams {
                    channel_id: "chshort".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad channel, name too long".to_string(),
                params: OpenTryParams {
                    channel_id: "abcdefghijkasdfasdfasdfasgdasdgasdfasdfadflmnoasdasdasdfasdfasdfasdfadadgadgadsfpqrstu".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Empty counterparty version".to_string(),
                params: OpenTryParams {
                    counterparty_version: " ".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad proof height, height = 0".to_string(),
                params: OpenTryParams {
                    proof_height: Height {
                        version_number: 0,
                        version_height: 0,
                    },
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad order".to_string(),
                params: OpenTryParams {
                    order: 99,
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct connection hops (connection id)".to_string(),
                params: OpenTryParams {
                    connection_hops: vec!["connection124".to_string()].into_iter().collect(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad connection hops, connection id too long".to_string(),
                params: OpenTryParams {
                    connection_hops: vec!["abcdefghadvvxvczxcvzxvxvzxvcsddsfsdsdfasdfasfasdasdgasdfasdfasdfadsfasdfijklmnopqrstu".to_string()]
                        .into_iter()
                        .collect(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad connection hops, connection id too short".to_string(),
                params: OpenTryParams {
                    connection_hops: vec!["connid".to_string()].into_iter().collect(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            // Currently failing because we don't validate connection hops
            // Test {
            //     name: "Bad connection hops, more than 1".to_string(),
            //     params: OpenTryParams {
            //         connection_hops: vec!["connectionhop".to_string(), "connectionhopnext".to_string()].into_iter().collect(),
            //         ..default_params.clone()
            //     },
            //     want_pass: false,
            // },
            Test {
                name: "Empty channel version".to_string(),
                params: OpenTryParams {
                    channel_version: " ".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad counterparty port, name too long".to_string(),
                params: OpenTryParams {
                    counterparty_port_id: "abcdefgaszdsfgasdasdvsdfasdfasdfdfasdfasdfadsgasdfasdfasdfasdfasdfasdfhijklmnopqrstu".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct counterparty channel identifier".to_string(),
                params: OpenTryParams {
                    counterparty_channel_id: "channelid34".to_string(),
                    ..default_params
                },
                want_pass: true,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let p = test.params.clone();

            let msg = MsgChannelOpenTry::new(
                p.port_id,
                p.channel_id,
                p.channel_version,
                p.order,
                p.connection_hops,
                p.counterparty_port_id,
                p.counterparty_channel_id,
                p.counterparty_version,
                p.proof_init,
                p.proof_height,
                acc,
            );

            assert_eq!(
                test.want_pass,
                msg.is_ok(),
                "MsgChanOpenTry::new failed for test {}, \nmsg {:?} with error {:?}",
                test.name,
                test.params.clone(),
                msg.err(),
            );
        }
    }

    #[test]
    fn parse_channel_open_ack_msg() {
        let id_hex = "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C";
        let acc = AccountId::from_str(id_hex).unwrap();

        #[derive(Clone, Debug, PartialEq)]
        struct OpenAckParams {
            port_id: String,
            channel_id: String,
            counterparty_version: String,
            proof_try: CommitmentProof,
            proof_height: Height,
        }

        let default_params = OpenAckParams {
            port_id: "port".to_string(),
            channel_id: "testchannel".to_string(),
            counterparty_version: "1.0".to_string(),
            proof_try: get_dummy_proof().into(),
            proof_height: Height {
                version_number: 0,
                version_height: 10,
            },
        };

        struct Test {
            name: String,
            params: OpenAckParams,
            want_pass: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                params: default_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Correct port identifier".to_string(),
                params: OpenAckParams {
                    port_id: "p34".to_string(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad port, name too short".to_string(),
                params: OpenAckParams {
                    port_id: "p".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad port, name too long".to_string(),
                params: OpenAckParams {
                    port_id: "abcdezdfDfsdfgfddsfsfdsdfdfvxcvzxcvsgdfsdfwefwvsdfdsfdasgagadgsadgsdffghijklmnopqrstu".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct channel identifier".to_string(),
                params: OpenAckParams {
                    channel_id: "channelid34".to_string(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad channel, name too short".to_string(),
                params: OpenAckParams {
                    channel_id: "chshort".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad channel, name too long".to_string(),
                params: OpenAckParams {
                    channel_id: "abcdefghsdfasdfasfdasfdwewefsdfasdfasdfasdfasdfasdfsfdijklmnopqrstu".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Empty counterparty version".to_string(),
                params: OpenAckParams {
                    counterparty_version: " ".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad proof height, height = 0".to_string(),
                params: OpenAckParams {
                    proof_height: Height {
                        version_number: 0,
                        version_height: 0,
                    },
                    ..default_params
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let p = test.params.clone();

            let msg = MsgChannelOpenAck::new(
                p.port_id,
                p.channel_id,
                p.counterparty_version,
                p.proof_try,
                p.proof_height,
                acc,
            );

            assert_eq!(
                test.want_pass,
                msg.is_ok(),
                "MsgChanOpenAck::new failed for test {}, \nmsg {:?} with error {:?}",
                test.name,
                test.params.clone(),
                msg.err(),
            );
        }
    }

    #[test]
    fn parse_channel_open_confirm_msg() {
        let id_hex = "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C";
        let acc = AccountId::from_str(id_hex).unwrap();

        #[derive(Clone, Debug, PartialEq)]
        struct OpenConfirmParams {
            port_id: String,
            channel_id: String,
            proof_ack: CommitmentProof,
            proof_height: Height,
        }

        let default_params = OpenConfirmParams {
            port_id: "port".to_string(),
            channel_id: "testchannel".to_string(),
            proof_ack: get_dummy_proof().into(),
            proof_height: Height {
                version_number: 0,
                version_height: 10,
            },
        };

        struct Test {
            name: String,
            params: OpenConfirmParams,
            want_pass: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                params: default_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Correct port".to_string(),
                params: OpenConfirmParams {
                    port_id: "p34".to_string(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad port, name too short".to_string(),
                params: OpenConfirmParams {
                    port_id: "p".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad port, name too long".to_string(),
                params: OpenConfirmParams {
                    port_id: "abcdesdfasdsdffasdfasdfasfasdgasdfgasdfasdfasdfasdfasdfasdffghijklmnopqrstu".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct channel identifier".to_string(),
                params: OpenConfirmParams {
                    channel_id: "channelid34".to_string(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad channel, name too short".to_string(),
                params: OpenConfirmParams {
                    channel_id: "chshort".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad channel, name too long".to_string(),
                params: OpenConfirmParams {
                    channel_id: "abcdefghijklmnoasdfasdfasdfasdfasdgsdghasdfasdfasdfasdfadsfasgdasdfasdfasfdpqrstu".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad proof height, height = 0".to_string(),
                params: OpenConfirmParams {
                    proof_height: Height {
                        version_number: 0,
                        version_height: 0,
                    },
                    ..default_params
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let p = test.params.clone();

            let msg = MsgChannelOpenConfirm::new(
                p.port_id,
                p.channel_id,
                p.proof_ack,
                p.proof_height,
                acc,
            );

            assert_eq!(
                test.want_pass,
                msg.is_ok(),
                "MsgChanOpenConfirm::new failed for test {}, \nmsg {:?} with error {:?}",
                test.name,
                test.params.clone(),
                msg.err(),
            );
        }
    }

    #[test]
    fn parse_channel_close_init_msg() {
        let id_hex = "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C";
        let acc = AccountId::from_str(id_hex).unwrap();

        #[derive(Clone, Debug, PartialEq)]
        struct CloseInitParams {
            port_id: String,
            channel_id: String,
        }

        let default_params = CloseInitParams {
            port_id: "port".to_string(),
            channel_id: "testchannel".to_string(),
        };

        struct Test {
            name: String,
            params: CloseInitParams,
            want_pass: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                params: default_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Correct port".to_string(),
                params: CloseInitParams {
                    port_id: "p34".to_string(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad port, name too short".to_string(),
                params: CloseInitParams {
                    port_id: "p".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad port, name too long".to_string(),
                params: CloseInitParams {
                    port_id: "abcdefsdfasdfasdfasdfasdfasdfadsfasdgafsgadfasdfasdfasdfsdfasdfaghijklmnopqrstu".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct channel identifier".to_string(),
                params: CloseInitParams {
                    channel_id: "channelid34".to_string(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad channel, name too short".to_string(),
                params: CloseInitParams {
                    channel_id: "chshort".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad channel, name too long".to_string(),
                params: CloseInitParams {
                    channel_id: "abcdeasdfasdfasdfasdfasdfasdfasdfasdfdgasdfasdfasdfghijklmnopqrstu".to_string(),
                    ..default_params
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let p = test.params.clone();

            let msg = MsgChannelCloseInit::new(p.port_id, p.channel_id, acc);

            assert_eq!(
                test.want_pass,
                msg.is_ok(),
                "MsgChanCloseInit::new failed for test {}, \nmsg {:?} with error {:?}",
                test.name,
                test.params.clone(),
                msg.err(),
            );
        }
    }

    #[test]
    fn parse_channel_close_confirm_msg() {
        let id_hex = "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C";
        let acc = AccountId::from_str(id_hex).unwrap();

        #[derive(Clone, Debug, PartialEq)]
        struct CloseConfirmParams {
            port_id: String,
            channel_id: String,
            proof_init: CommitmentProof,
            proof_height: Height,
        }

        let default_params = CloseConfirmParams {
            port_id: "port".to_string(),
            channel_id: "testchannel".to_string(),
            proof_init: get_dummy_proof().into(),
            proof_height: Height {
                version_number: 0,
                version_height: 10,
            },
        };

        struct Test {
            name: String,
            params: CloseConfirmParams,
            want_pass: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                params: default_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Correct port".to_string(),
                params: CloseConfirmParams {
                    port_id: "p34".to_string(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad port, name too short".to_string(),
                params: CloseConfirmParams {
                    port_id: "p".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad port, name too long".to_string(),
                params: CloseConfirmParams {
                    port_id:
                        "abcdefghijklmnsdfasdfasdfasdfasdgafgadsfasdfasdfasdasfdasdfsadfopqrstu"
                            .to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Correct channel identifier".to_string(),
                params: CloseConfirmParams {
                    channel_id: "channelid34".to_string(),
                    ..default_params.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Bad channel, name too short".to_string(),
                params: CloseConfirmParams {
                    channel_id: "chshort".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad channel, name too long".to_string(),
                params: CloseConfirmParams {
                    channel_id:
                        "abcdefghiasdfadsfasdfgdfsadfasdasdfasdasdfasddsfasdfasdjklmnopqrstu"
                            .to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad proof height, height = 0".to_string(),
                params: CloseConfirmParams {
                    proof_height: Height {
                        version_number: 0,
                        version_height: 0,
                    },
                    ..default_params
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let p = test.params.clone();

            let msg = MsgChannelCloseConfirm::new(
                p.port_id,
                p.channel_id,
                p.proof_init,
                p.proof_height,
                acc,
            );

            assert_eq!(
                test.want_pass,
                msg.is_ok(),
                "MsgChanCloseConfirm::new failed for test {}, \nmsg {:?} with error {:?}",
                test.name,
                test.params.clone(),
                msg.err(),
            );
        }
    }
}
