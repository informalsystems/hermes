//! TODO

use std::time::Duration;

use abscissa_core::tracing::info;

use relayer::{
    chain::{Chain, CosmosSDKChain},
    client::LightClient,
    config::Config,
};

use crate::prelude::*;

/// TODO
pub async fn start(config: &Config, chains: Vec<CosmosSDKChain>) -> Result<(), BoxError> {
    for chain in &chains {
        let light_client = chain.light_client().ok_or_else(|| {
            format!(
                "light client for chain {} has not been initialized",
                chain.id()
            )
        })?;

        if let Some(latest_trusted) = light_client.latest_trusted().await? {
            info!(
                chain.id = %chain.id(),
                "latest trusted state is at height {:?}",
                latest_trusted.height(),
            );
        } else {
            warn!(
                chain.id = %chain.id(),
                "no latest trusted state",
            );
        }
    }

    let mut interval = tokio::time::interval(Duration::from_secs(2));

    loop {
        interval.tick().await;
    }
}
