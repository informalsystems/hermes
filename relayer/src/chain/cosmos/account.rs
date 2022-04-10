use core::fmt;

use ibc_proto::cosmos::auth::v1beta1::BaseAccount;
use prost::Message;
use tonic::metadata::MetadataValue;

use crate::error::Error;

use super::CosmosSdkChain;

/// Wrapper for account number and sequence number.
///
/// More fields may be added later.
#[derive(Clone, Debug, PartialEq)]
pub struct Account {
    // pub address: String,
    // pub pub_key: Option<prost_types::Any>,
    pub number: AccountNumber,
    pub sequence: AccountSequence,
}

impl From<BaseAccount> for Account {
    fn from(value: BaseAccount) -> Self {
        Self {
            number: AccountNumber::new(value.account_number),
            sequence: AccountSequence::new(value.sequence),
        }
    }
}

/// Newtype for account numbers
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct AccountNumber(u64);

impl AccountNumber {
    pub fn new(number: u64) -> Self {
        Self(number)
    }

    pub fn to_u64(self) -> u64 {
        self.0
    }
}

impl fmt::Display for AccountNumber {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// Newtype for account sequence numbers
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct AccountSequence(u64);

impl AccountSequence {
    pub fn new(sequence: u64) -> Self {
        Self(sequence)
    }

    pub fn to_u64(self) -> u64 {
        self.0
    }

    pub fn increment(self) -> Self {
        Self(self.0 + 1)
    }
}

impl fmt::Display for AccountSequence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// Uses the GRPC client to retrieve the account sequence
pub async fn query_account(chain: &CosmosSdkChain, address: String) -> Result<BaseAccount, Error> {
    use ibc_proto::cosmos::auth::v1beta1::query_client::QueryClient;
    use ibc_proto::cosmos::auth::v1beta1::{EthAccount, QueryAccountRequest};

    crate::telemetry!(query, &chain.config.id, "query_account");

    let mut client = QueryClient::connect(chain.grpc_addr.clone())
        .await
        .map_err(Error::grpc_transport)?;

    let mut request = tonic::Request::new(QueryAccountRequest {
        address: address.clone(),
    });
    request.metadata_mut().insert(
        "authorization",
        MetadataValue::from_str("Auth-Header").unwrap(),
    );

    let response = client.account(request).await;

    // Querying for an account might fail, i.e. if the account doesn't actually exist
    let resp_account = match response.map_err(Error::grpc_status)?.into_inner().account {
        Some(account) => account,
        None => return Err(Error::empty_query_account(address)),
    };

    if resp_account.type_url == "/cosmos.auth.v1beta1.BaseAccount" {
        Ok(BaseAccount::decode(resp_account.value.as_slice())
            .map_err(|e| Error::protobuf_decode("BaseAccount".to_string(), e))?)
    } else if resp_account.type_url.ends_with(".EthAccount") {
        Ok(EthAccount::decode(resp_account.value.as_slice())
            .map_err(|e| Error::protobuf_decode("EthAccount".to_string(), e))?
            .base_account
            .ok_or_else(Error::empty_base_account)?)
    } else {
        Err(Error::unknown_account_type(resp_account.type_url))
    }
}
