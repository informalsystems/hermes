use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;

use crate::cosmos::error::Error;

pub type CosmosRuntimeContext = TokioRuntimeContext<Error>;
