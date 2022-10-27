use http::uri::Uri;

use ibc_proto::cosmos::bank::v1beta1::{
    query_client::QueryClient, QueryAllBalancesRequest, QueryBalanceRequest,
};

use crate::{account::Balance, error::Error};

/// Uses the GRPC client to retrieve the account balance for a specific denom
pub async fn query_balance(
    grpc_address: &Uri,
    account_address: &str,
    denom: &str,
) -> Result<Balance, Error> {
    let mut client = QueryClient::connect(grpc_address.clone())
        .await
        .map_err(Error::grpc_transport)?;

    let request = tonic::Request::new(QueryBalanceRequest {
        address: account_address.to_string(),
        denom: denom.to_string(),
    });

    let response = client
        .balance(request)
        .await
        .map(|r| r.into_inner())
        .map_err(Error::grpc_status)?;

    // Querying for a balance might fail, i.e. if the account doesn't actually exist
    let balance = response
        .balance
        .ok_or_else(|| Error::empty_query_account(account_address.to_string()))?;

    Ok(Balance {
        amount: balance.amount,
        denom: balance.denom,
    })
}

/// Uses the GRPC client to retrieve the account balance for all denom
pub async fn query_all_balances(
    grpc_address: &Uri,
    account_address: &str,
) -> Result<Vec<Balance>, Error> {
    let mut client = QueryClient::connect(grpc_address.clone())
        .await
        .map_err(Error::grpc_transport)?;

    let request = tonic::Request::new(QueryAllBalancesRequest {
        address: account_address.to_string(),
        pagination: None,
    });

    let response = client
        .all_balances(request)
        .await
        .map(|r| r.into_inner())
        .map_err(Error::grpc_status)?;

    let balances = response
        .balances
        .into_iter()
        .map(|balance| Balance {
            amount: balance.amount,
            denom: balance.denom,
        })
        .collect();

    Ok(balances)
}
