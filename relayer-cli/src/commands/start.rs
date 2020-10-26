use std::ops::Deref;

use abscissa_core::{
    application::fatal_error, error::BoxError, tracing::info, Command, Options, Runnable,
};

use relayer::{
    chain::CosmosSDKChain,
    config::{Config, LightClientConfig},
};

use crate::{application::APPLICATION, prelude::*, tasks};

#[derive(Command, Debug, Options)]
pub struct StartCmd {
    #[options(help = "reset state from trust options", short = "r")]
    reset: bool,
}

impl StartCmd {
    async fn cmd(&self) -> Result<(), BoxError> {
        let config = app_config().clone();
        dbg!(&config);
        start(config, self.reset).await
    }
}

impl Runnable for StartCmd {
    fn run(&self) {
        abscissa_tokio::run(&APPLICATION, async move {
            self.cmd()
                .await
                .unwrap_or_else(|e| fatal_error(app_reader().deref(), &*e));
        })
        .unwrap();
    }
}

async fn start(config: Config, reset: bool) -> Result<(), BoxError> {
    let chains: Vec<CosmosSDKChain> = vec![];

    for chain_config in &config.chains {
        let light_config: LightClientConfig = todo!();
        // let light_config = todo!().ok_or_else(|| {
        //     format!(
        //         "could not find light client configuration for chain {}",
        //         chain_config.id
        //     )
        // })?;

        info!(chain.id = %chain_config.id, "spawning light client");

        let mut chain = CosmosSDKChain::from_config(chain_config.clone())?;

        let client_task =
            tasks::light_client::create(&mut chain, light_config.clone(), reset).await?;

        chains.push(chain);

        let _handle = tokio::task::spawn(client_task);
    }

    tasks::relayer::start(&config, chains).await?;

    Ok(())
}
