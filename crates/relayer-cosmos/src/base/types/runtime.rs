use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;

use crate::base::error::Error;

pub type CosmosRuntimeContext = TokioRuntimeContext<Error>;
