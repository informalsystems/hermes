use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;

use crate::relayer_mock::base::error::Error;

pub type MockRuntimeContext = TokioRuntimeContext<Error>;
