#![allow(clippy::too_many_arguments)]
use super::channel::{ChannelEnd, Counterparty};
use super::exported::*;
use crate::ics04_channel::error::Kind;
use crate::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use crate::tx_msg::Msg;
use serde_derive::{Deserialize, Serialize};
use std::str::FromStr;
use tendermint::account::Id as AccountId;
use crate::ics23_commitment::CommitmentProof;
use crate::ics04_channel::packet::Packet;
use crate::ics03_connection::connection::validate_version;
use anomaly::fail;

// TODO: Validate Proof for all Msgs

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
        order: String,
        connection_hops: Vec<String>,
        counterparty_port_id: String,
        counterparty_channel_id: String,
        signer: AccountId,
    ) -> Result<MsgChannelOpenInit, crate::ics04_channel::error::Error> {
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
                order.parse()?,
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
    type ValidationError = crate::ics04_channel::error::Error;

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
    proof_init: CommitmentProof,
    proof_height: u64,
    signer: AccountId,
}

impl MsgChannelOpenTry {
    pub fn new(
        port_id: String,
        channel_id: String,
        channel_version: String,
        order: String,
        connection_hops: Vec<String>,
        counterparty_port_id: String,
        counterparty_channel_id: String,
        counterparty_version: String,
        proof_init: CommitmentProof,
        proof_height: u64,
        signer: AccountId,
    ) -> Result<MsgChannelOpenTry, crate::ics04_channel::error::Error> {
        if proof_height == 0 {
            fail!(Kind::InvalidHeight, "Height cannot be zero");
        }

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
                order.parse()?,
                Counterparty::new(counterparty_port_id, counterparty_channel_id)
                    .map_err(|e| Kind::IdentifierError.context(e))?,
                connection_hops.map_err(|e| Kind::IdentifierError.context(e))?,
                channel_version,
            ),
            counterparty_version: validate_version(counterparty_version)
                .map_err(|e| Kind::InvalidVersion.context(e))?,
            proof_init,
            proof_height,
            signer,
        })
    }
}

impl Msg for MsgChannelOpenTry {
    type ValidationError = crate::ics04_channel::error::Error;

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
    proof_try: CommitmentProof,
    proof_height: u64,
    signer: AccountId,
}

impl MsgChannelOpenAck {
    pub fn new(
        port_id: String,
        channel_id: String,
        counterparty_version: String,
        proof_try: CommitmentProof,
        proof_height: u64,
        signer: AccountId,
    ) -> Result<MsgChannelOpenAck, crate::ics04_channel::error::Error> {
        if proof_height == 0 {
            fail!(Kind::InvalidHeight, "Height cannot be zero");
        }

        Ok(Self {
            port_id: port_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel_id: channel_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            counterparty_version: validate_version(counterparty_version)
                .map_err(|e| Kind::InvalidVersion.context(e))?,
            proof_try,
            proof_height,
            signer,
        })
    }
}

impl Msg for MsgChannelOpenAck {
    type ValidationError = crate::ics04_channel::error::Error;

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
    proof_ack: CommitmentProof,
    proof_height: u64,
    signer: AccountId,
}

impl MsgChannelOpenConfirm {
    pub fn new(
        port_id: String,
        channel_id: String,
        proof_ack: CommitmentProof,
        proof_height: u64,
        signer: AccountId,
    ) -> Result<MsgChannelOpenConfirm, crate::ics04_channel::error::Error> {
        if proof_height == 0 {
            fail!(Kind::InvalidHeight, "Height cannot be zero");
        }

        Ok(Self {
            port_id: port_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel_id: channel_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            proof_ack,
            proof_height,
            signer,
        })
    }
}

impl Msg for MsgChannelOpenConfirm {
    type ValidationError = crate::ics04_channel::error::Error;

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
    ) -> Result<MsgChannelCloseInit, crate::ics04_channel::error::Error> {
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
    type ValidationError = crate::ics04_channel::error::Error;

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
    proof_init: CommitmentProof,
    proof_height: u64,
    signer: AccountId,
}

impl MsgChannelCloseConfirm {
    pub fn new(
        port_id: String,
        channel_id: String,
        proof_init: CommitmentProof,
        proof_height: u64,
        signer: AccountId,
    ) -> Result<MsgChannelCloseConfirm, crate::ics04_channel::error::Error> {
        if proof_height == 0 {
            fail!(Kind::InvalidHeight, "Height cannot be zero");
        }

        Ok(Self {
            port_id: port_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel_id: channel_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            proof_init,
            proof_height,
            signer,
        })
    }
}

impl Msg for MsgChannelCloseConfirm {
    type ValidationError = crate::ics04_channel::error::Error;

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
    proof: CommitmentProof,
    proof_height: u64,
    signer: AccountId,
}

impl MsgPacket {
    pub fn new(
        packet: Packet,
        proof: CommitmentProof,
        proof_height: u64,
        signer: AccountId,
    ) -> Result<MsgPacket, crate::ics04_channel::error::Error> {
        if proof_height == 0 {
            fail!(Kind::InvalidHeight, "Height cannot be zero");
        }

        Ok(Self {
            packet: packet.validate()
                .map_err(|e| Kind::InvalidPacket.context(e))?,
            proof,
            proof_height,
            signer,
        })
    }

    // returns the base64-encoded bytes used for the
    // data field when signing the packet
    pub fn get_data_bytes() -> Vec<u8> {todo!()}
}

impl Msg for MsgPacket {
    type ValidationError = crate::ics04_channel::error::Error;

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
    proof: CommitmentProof,
    proof_height: u64,
    signer: AccountId,
}

impl MsgTimeout {
    pub fn new(
        packet: Packet,
        next_sequence_recv: Option<u64>,
        proof: CommitmentProof,
        proof_height: u64,
        signer: AccountId,
    ) -> Result<MsgTimeout, crate::ics04_channel::error::Error> {
        if proof_height == 0 {
            fail!(Kind::InvalidHeight, "Height cannot be zero");
        }

        Ok(Self {
            packet: packet.validate()
                .map_err(|e| Kind::InvalidPacket.context(e))?,
            next_sequence_recv,
            proof,
            proof_height,
            signer,
        })
    }
}

impl Msg for MsgTimeout {
    type ValidationError = crate::ics04_channel::error::Error;

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
    proof: CommitmentProof,
    proof_height: u64,
    signer: AccountId,
}

impl MsgAcknowledgement {
    pub fn new(
        packet: Packet,
        acknowledgement: Vec<u8>,
        proof: CommitmentProof,
        proof_height: u64,
        signer: AccountId,
    ) -> Result<MsgAcknowledgement, crate::ics04_channel::error::Error> {
        if proof_height == 0 {
            fail!(Kind::InvalidHeight, "Height cannot be zero");
        }

        if acknowledgement.len() > 100 {
            fail!(Kind::AcknowledgementTooLong, "Acknowledgement cannot exceed 100 bytes")
        }

        Ok(Self {
            packet: packet.validate()
                .map_err(|e| Kind::InvalidPacket.context(e))?,
            acknowledgement,
            proof,
            proof_height,
            signer,
        })
    }
}

impl Msg for MsgAcknowledgement {
    type ValidationError = crate::ics04_channel::error::Error;

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
    use std::str::FromStr;
    use tendermint::account::Id as AccountId;

    #[test]
    fn parse_channel_open_init_msg() {
        use super::MsgChannelOpenInit;
        let id_hex = "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C";
        let acc = AccountId::from_str(id_hex).unwrap();

        #[derive(Clone, Debug, PartialEq)]
        struct OpenInitParams {
            port_id: String,
            channel_id: String,
            version: String,
            order: String,
            connection_hops: Vec<String>,
            counterparty_port_id: String,
            counterparty_channel_id: String,
        }

        let default_params = OpenInitParams {
            port_id: "port".to_string(),
            channel_id: "testchannel".to_string(),
            version: "1.0".to_string(),
            order: "ORDERED".to_string(),
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
                name: "Bad port, non-alpha".to_string(),
                params: OpenInitParams {
                    port_id: "p34".to_string(),
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
                    order: "MYORER".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad connection hops".to_string(),
                params: OpenInitParams {
                    connection_hops: vec!["conn124".to_string()].into_iter().collect(),
                    ..default_params.clone()
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

            match msg {
                Ok(_res) => {
                    assert!(
                        test.want_pass,
                        "MsgChanOpenInit::new should have failed for test {}, \nmsg {:?}",
                        test.name,
                        test.params.clone()
                    );
                }
                Err(err) => {
                    assert!(
                        !test.want_pass,
                        "MsgChanOpenInit::new failed for test {}, \nmsg {:?} with err {:?}",
                        test.name,
                        test.params.clone(),
                        err
                    );
                }
            }
        }
    }
}
