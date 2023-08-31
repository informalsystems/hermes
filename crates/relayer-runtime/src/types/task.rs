use tokio::task::JoinHandle;

pub struct TokioTaskHandle(pub JoinHandle<()>);
