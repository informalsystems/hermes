use crate::ics03_connection::connection::Counterparty;
use crate::ics03_connection::error::Kind;
use crate::ics03_connection::exported::ConnectionCounterparty;
use crate::ics04_channel::msgs::Msg;
use crate::ics23_commitment::CommitmentPrefix;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::ics24_host::validate::{validate_client_identifier, validate_connection_identifier};
use serde_derive::{Deserialize, Serialize};
use tendermint::account::Id as AccountId;

pub const TYPE_MSG_CONNECTION_OPEN_INIT: &str = "connection_open_init";

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgConnectionOpenInit {
    connection_id: ConnectionId,
    client_id: ClientId,
    counterparty: Counterparty,
    signer: AccountId,
}

impl MsgConnectionOpenInit {
    pub fn new(
        connection_id: String,
        client_id: String,
        counterparty_connection_id: String,
        counterparty_client_id: String,
        counterparty_commitment_prefix: CommitmentPrefix,
        signer: AccountId,
    ) -> Result<MsgConnectionOpenInit, crate::ics03_connection::error::Error> {
        Ok(Self {
            connection_id: connection_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            client_id: client_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            counterparty: Counterparty::new(
                counterparty_client_id,
                counterparty_connection_id,
                counterparty_commitment_prefix,
            )
            .map_err(|e| Kind::IdentifierError.context(e))?,
            signer,
        })
    }
}

impl Msg for MsgConnectionOpenInit {
    type ValidationError = crate::ics03_connection::error::Error;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_CONNECTION_OPEN_INIT.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        validate_connection_identifier(self.connection_id.as_str())
            .map_err(|e| Kind::IdentifierError.context(e))?;
        validate_client_identifier(self.client_id.as_str())
            .map_err(|e| Kind::IdentifierError.context(e))?;
        self.counterparty
            .validate_basic()
            .map_err(|e| Kind::IdentifierError.context(e))?;
        //todo: validate signer!
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
    use crate::ics23_commitment::CommitmentPrefix;
    use std::str::FromStr;
    use tendermint::account::Id as AccountId;

    #[test]
    fn parse_connection_open_init_msg() {
        use super::MsgConnectionOpenInit;
        let id_hex = "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C";
        let acc = AccountId::from_str(id_hex).unwrap();

        #[derive(Clone, Debug, PartialEq)]
        struct ConOpenInitParams {
            connection_id: String,
            client_id: String,
            counterparty_connection_id: String,
            counterparty_client_id: String,
            counterparty_commitment_prefix: CommitmentPrefix,
        }

        let default_con_params = ConOpenInitParams {
            connection_id: "srcconnection".to_string(),
            client_id: "srcclient".to_string(),
            counterparty_connection_id: "destconnection".to_string(),
            counterparty_client_id: "destclient".to_string(),
            counterparty_commitment_prefix: CommitmentPrefix {},
        };

        struct Test {
            name: String,
            params: ConOpenInitParams,
            want_pass: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                params: default_con_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Bad connection id, non-alpha".to_string(),
                params: ConOpenInitParams {
                    connection_id: "con007".to_string(),
                    ..default_con_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad client id, name too short".to_string(),
                params: ConOpenInitParams {
                    client_id: "client".to_string(),
                    ..default_con_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad destination connection id, name too long".to_string(),
                params: ConOpenInitParams {
                    counterparty_connection_id: "abcdefghijklmnopqrstu".to_string(),
                    ..default_con_params.clone()
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let p = test.params.clone();

            let msg = MsgConnectionOpenInit::new(
                p.connection_id,
                p.client_id,
                p.counterparty_connection_id,
                p.counterparty_client_id,
                p.counterparty_commitment_prefix,
                acc,
            );

            match msg {
                Ok(_res) => {
                    assert!(
                        test.want_pass,
                        "MsgConnOpenInit::new should have failed for test {}, \nmsg {:?}",
                        test.name,
                        test.params.clone()
                    );
                }
                Err(_err) => {
                    assert!(
                        !test.want_pass,
                        "MsgConnOpenInit::new failed for test {}, \nmsg {:?}",
                        test.name,
                        test.params.clone()
                    );
                }
            }
        }
    }
}
