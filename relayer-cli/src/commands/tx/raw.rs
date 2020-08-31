use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};
use relayer::config::{ChainConfig, Config};
use ibc::ics24_host::identifier::{ClientId, ConnectionId};
use ibc::ics24_host::error::ValidationError;
use tendermint::chain::Id as ChainId;
use relayer::chain::{CosmosSDKChain, Chain};

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawConnInitCmd {
    #[options(free, help = "identifier of the local chain")]
    local_chain_id: Option<ChainId>,

    #[options(free, help = "identifier of the remote chain")]
    remote_chain_id: Option<ChainId>,

    #[options(free, help = "identifier of the local client")]
    local_client_id: Option<String>,

    #[options(free, help = "identifier of the remote client")]
    remote_client_id: Option<String>,

    #[options(free, help = "identifier of the local connection")]
    local_connection_id: Option<String>,

    #[options(free, help = "identifier of the remote connection")]
    remote_connection_id: Option<String>
}

#[derive(Debug)]
struct MsgConnectionOpenInitOptions {
    local_client_id: ClientId,
    remote_client_id: ClientId,
    local_connection_id: ConnectionId,
    remote_connection_id: ConnectionId
}

impl TxRawConnInitCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, MsgConnectionOpenInitOptions), String> {
        let local_chain_id = self
            .local_chain_id
            .ok_or_else(|| "missing local chain identifier".to_string())?;

        let local_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == local_chain_id)
            .ok_or_else(|| "missing local chain configuration".to_string())?;

        let remote_chain_id = self
            .remote_chain_id
            .ok_or_else(|| "missing remote chain identifier".to_string())?;

        let remote_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == remote_chain_id)
            .ok_or_else(|| "missing remote chain configuration".to_string())?;

        let local_client_id = self
            .local_client_id
            .as_ref()
            .ok_or_else(|| "missing local client identifier".to_string())?
            .parse()
            .map_err(|err: ValidationError| err.to_string())?;

        let local_connection_id = self
            .local_connection_id
            .as_ref()
            .ok_or_else(|| "missing local connection identifier".to_string())?
            .parse()
            .map_err(|err: ValidationError| err.to_string())?;

        let remote_client_id = self
            .remote_client_id
            .as_ref()
            .ok_or_else(|| "missing remote client identifier".to_string())?
            .parse()
            .map_err(|err: ValidationError| err.to_string())?;

        let remote_connection_id = self
            .remote_connection_id
            .as_ref()
            .ok_or_else(|| "missing remote connection identifier".to_string())?
            .parse()
            .map_err(|err: ValidationError| err.to_string())?;

        let opts = MsgConnectionOpenInitOptions {
            local_client_id,
            local_connection_id,
            remote_client_id,
            remote_connection_id
        };
        Ok((local_chain_config.clone(), opts))
    }
}


impl Runnable for TxRawConnInitCmd {
    fn run(&self) {
        let config = app_config();

        let (chain_config, msg) = match self.validate_options(&config) {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };
        status_info!("Message", "{:?}", msg);

        let chain = CosmosSDKChain::from_config(chain_config).unwrap();
        let signed = chain.build_sign_tx(vec![msg]);


        // match res {
        //     Ok(cs) => status_info!("Result for channel end query: ", "{:?}", cs),
        //     Err(e) => status_info!("Error encountered on channel end query:", "{}", e),
        // }
    }
}
