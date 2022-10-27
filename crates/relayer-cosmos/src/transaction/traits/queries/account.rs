use async_trait::async_trait;
use ibc_relayer::chain::cosmos::types::account::Account;
use ibc_relayer_framework::base::core::traits::error::HasError;

#[async_trait]
pub trait CanQueryAccount: HasError {
    async fn query_account(&self) -> Result<Account, Self::Error>;
}

#[async_trait]
pub trait AccountQuerier<Context>
where
    Context: HasError,
{
    async fn query_account(context: &Context) -> Result<Account, Context::Error>;
}
