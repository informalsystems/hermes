use async_trait::async_trait;
use ibc_proto::cosmos::auth::v1beta1::query_client::QueryClient;
use ibc_proto::cosmos::auth::v1beta1::QueryAccountRequest;
use ibc_relayer::chain::cosmos::types::account::Account;
use ibc_relayer_framework::base::core::traits::error::{HasError, InjectError};
use tonic::transport::Error as TransportError;
use tonic::{Request, Status};

use crate::transaction::traits::account::{HasAccount, MaybeHasAccount};
use crate::transaction::traits::decoders::account::CanDecodeAccount;
use crate::transaction::traits::fields::{HasGrpcAddress, HasKeyEntry};
use crate::transaction::traits::queries::account::AccountQuerier;

pub struct BaseAccountQuerier;

pub struct MaybeAccountQuerier;

pub struct ReturnAccountFromContext;

pub trait InjectQueryAccountError: HasError {
    fn address_not_found_error(address: &str) -> Self::Error;
}

#[async_trait]
impl<Context> AccountQuerier<Context> for BaseAccountQuerier
where
    Context: InjectError<Status> + InjectError<TransportError> + InjectQueryAccountError,
    Context: HasGrpcAddress + HasKeyEntry,
    Context: CanDecodeAccount,
{
    async fn query_account(context: &Context) -> Result<Account, Context::Error> {
        let grpc_address = context.grpc_address();
        let key_entry = context.key_entry();
        let account_address = &key_entry.account;

        let mut client = QueryClient::connect(grpc_address.clone())
            .await
            .map_err(Context::inject_error)?;

        let request = Request::new(QueryAccountRequest {
            address: account_address.to_string(),
        });

        let response = client.account(request).await;

        // Querying for an account might fail, i.e. if the account doesn't actually exist
        let raw_account = match response
            .map_err(Context::inject_error)?
            .into_inner()
            .account
        {
            Some(account) => account,
            None => return Err(Context::address_not_found_error(account_address)),
        };

        let account = context.decode_account(raw_account)?;

        Ok(account.into())
    }
}

#[async_trait]
impl<Context> AccountQuerier<Context> for MaybeAccountQuerier
where
    Context: HasError,
    Context: MaybeHasAccount,
    BaseAccountQuerier: AccountQuerier<Context>,
{
    async fn query_account(context: &Context) -> Result<Account, Context::Error> {
        let m_account = context.maybe_account();

        match m_account {
            Some(account) => Ok(account.clone()),
            None => {
                let account = BaseAccountQuerier::query_account(context).await?;
                context.update_account(&account);
                Ok(account)
            }
        }
    }
}

#[async_trait]
impl<Context> AccountQuerier<Context> for ReturnAccountFromContext
where
    Context: HasError,
    Context: HasAccount,
{
    async fn query_account(context: &Context) -> Result<Account, Context::Error> {
        Ok(context.account().clone())
    }
}
