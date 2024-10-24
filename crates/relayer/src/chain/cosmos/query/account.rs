use http::uri::Uri;
use ibc_proto::cosmos::auth::v1beta1::query_client::QueryClient;
use ibc_proto::cosmos::auth::v1beta1::{BaseAccount, QueryAccountRequest};
use prost::Message;
use tracing::info;

use crate::chain::cosmos::types::account::Account;
use crate::config::default::max_grpc_decoding_size;
use crate::error::Error;
use crate::util::create_grpc_client;

/// EthAccount defines an Ethermint account.
/// TODO: remove when/if a canonical `EthAccount`
/// lands in the next Cosmos SDK release
/// (note https://github.com/cosmos/cosmos-sdk/pull/9981
/// only adds the PubKey type)
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct EthAccount {
    #[prost(message, optional, tag = "1")]
    pub base_account: ::core::option::Option<BaseAccount>,
    #[prost(bytes = "vec", tag = "2")]
    pub code_hash: ::prost::alloc::vec::Vec<u8>,
}

/// Get a `&mut Account` from an `&mut Option<Account>` if it is `Some(Account)`.
/// Otherwise query for the account information, update the `Option` to `Some`,
/// and return the underlying `&mut` reference.
pub async fn get_or_fetch_account<'a>(
    grpc_address: &'a Uri,
    account_address: &'a str,
    m_account: &'a mut Option<Account>,
) -> Result<&'a mut Account, Error> {
    match m_account {
        Some(account) => Ok(account),
        None => {
            let account = query_account(grpc_address, account_address).await?;
            *m_account = Some(account.into());

            Ok(m_account
                .as_mut()
                .expect("account was supposedly just cached"))
        }
    }
}

/// Refresh the account sequence behind the `&mut Account` by refetching the
/// account and updating the `&mut` reference.
pub async fn refresh_account<'a>(
    grpc_address: &Uri,
    account_address: &str,
    m_account: &'a mut Account,
) -> Result<(), Error> {
    let account = query_account(grpc_address, account_address).await?;

    info!(
        old = %m_account.sequence,
        new = %account.sequence,
        "refreshed account sequence number",
    );

    *m_account = account.into();

    Ok(())
}

/// Uses the GRPC client to retrieve the account sequence
pub async fn query_account(
    grpc_address: &Uri,
    account_address: &str,
) -> Result<BaseAccount, Error> {
    let mut client = create_grpc_client(grpc_address, QueryClient::new).await?;

    client = client.max_decoding_message_size(max_grpc_decoding_size().get_bytes() as usize);

    let request = tonic::Request::new(QueryAccountRequest {
        address: account_address.to_string(),
    });

    let response = client.account(request).await;

    // Querying for an account might fail, i.e. if the account doesn't actually exist
    let resp_account = match response
        .map_err(|e| Error::grpc_status(e, "query_account".to_owned()))?
        .into_inner()
        .account
    {
        Some(account) => account,
        None => return Err(Error::empty_query_account(account_address.to_string())),
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
