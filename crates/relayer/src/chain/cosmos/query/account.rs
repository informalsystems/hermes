use http::uri::Uri;
use ibc_proto::cosmos::auth::v1beta1::query_client::QueryClient;
use ibc_proto::cosmos::auth::v1beta1::{BaseAccount, EthAccount, QueryAccountRequest};
use prost::Message;
use tracing::info;

use crate::chain::cosmos::types::account::Account;
use crate::error::Error;

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
        sequence = %account.sequence,
        number = %account.account_number,
        "refresh: retrieved account",
    );

    *m_account = account.into();

    Ok(())
}

/// Uses the GRPC client to retrieve the account sequence
pub async fn query_account(
    grpc_address: &Uri,
    account_address: &str,
) -> Result<BaseAccount, Error> {
    let mut client = QueryClient::connect(grpc_address.clone())
        .await
        .map_err(Error::grpc_transport)?;

    let request = tonic::Request::new(QueryAccountRequest {
        address: account_address.to_string(),
    });

    let response = client.account(request).await;

    // Querying for an account might fail, i.e. if the account doesn't actually exist
    let resp_account = match response.map_err(Error::grpc_status)?.into_inner().account {
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
