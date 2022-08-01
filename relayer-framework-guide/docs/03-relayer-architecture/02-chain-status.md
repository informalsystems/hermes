# Chain Status Component

## Abstract Chain Status Type

```rust
# use ibc_relayer_framework::traits::core::Async;
# use ibc_relayer_framework::traits::chain_context::ChainContext;
#
trait ChainStatus<Context: ChainContext>: Async {
    fn height(&self) -> &Context::Height;

    fn timestamp(&self) -> &Context::Timestamp;
}
```

## Chain Status Type in Chain Context

```rust
# use ibc_relayer_framework::traits::chain_context::ChainContext;
# use ibc_relayer_framework::traits::queries::status::ChainStatus;
#
trait ChainStatusContext: ChainContext {
    type ChainStatus: ChainStatus<Self>;
}
```

## Chain Status Querier Component

```rust
# use async_trait::async_trait;
# use ibc_relayer_framework::traits::chain_context::ChainContext;
# use ibc_relayer_framework::traits::queries::status::{ChainStatus, ChainStatusContext};
#
#[async_trait]
pub trait ChainStatusQuerier<Context: ChainStatusContext> {
    async fn query_chain_status(context: &Context) -> Result<Context::ChainStatus, Context::Error>;
}
```

## Cosmos Chain Status

```rust
# use async_trait::async_trait;
# use ibc_relayer_framework::traits::core::Async;
# use ibc_relayer_framework::traits::chain_context::ChainContext;
# use ibc_relayer_cosmos::cosmos::context::chain::CosmosChainContext;
#
#
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_relayer::chain::endpoint::ChainStatus as CosmosChainStatus;

# trait ChainStatus<Context: ChainContext> {
#     fn height(&self) -> &Context::Height;
#
#     fn timestamp(&self) -> &Context::Timestamp;
# }
#
# trait ChainStatusContext: ChainContext {
#     type ChainStatus: ChainStatus<Self>;
# }
#
impl<Chain> ChainStatus<CosmosChainContext<Chain>> for CosmosChainStatus
where
    Chain: Async,
{
    fn height(&self) -> &Height {
        &self.height
    }

    fn timestamp(&self) -> &Timestamp {
        &self.timestamp
    }
}

impl<Chain: Async> ChainStatusContext for CosmosChainContext<Chain> {
    type ChainStatus = CosmosChainStatus;
}
```

## Cosmos Chain Status Querier

```rust
# use async_trait::async_trait;
# use ibc_relayer::chain::handle::ChainHandle;
# use ibc_relayer::chain::endpoint::ChainStatus as CosmosChainStatus;
# use ibc_relayer_framework::traits::queries::status::ChainStatusQuerier;
# use ibc_relayer_cosmos::cosmos::context::chain::CosmosChainContext;
# use ibc_relayer_cosmos::cosmos::error::Error;
#
struct CosmosChainStatusQuerier;

#[async_trait]
impl<Chain> ChainStatusQuerier<CosmosChainContext<Chain>> for CosmosChainStatusQuerier
where
    Chain: ChainHandle,
{
    async fn query_chain_status(
        context: &CosmosChainContext<Chain>,
    ) -> Result<CosmosChainStatus, Error> {
        let status = context
            .handle
            .query_application_status()
            .map_err(Error::relayer)?;

        Ok(status)
    }
}
```
