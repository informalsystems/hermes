use crate::cosmos::error::Error;
use crate::tokio::context::TokioRuntimeContext;

pub type CosmosRuntimeContext = TokioRuntimeContext<Error>;
