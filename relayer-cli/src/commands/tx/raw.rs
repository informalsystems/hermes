use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};
use relayer::config::{ChainConfig, Config};
use tendermint::chain::Id as ChainId;
use tendermint::account::Id;
use relayer::chain::{CosmosSDKChain, Chain};
use ibc::ics03_connection::msgs::MsgConnectionOpenInit;
use ibc::ics23_commitment::CommitmentPrefix;
use ibc::tx_msg::Msg;

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

impl TxRawConnInitCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, MsgConnectionOpenInit), String> {
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
            .local_client_id.as_ref()
            .ok_or_else(|| "missing local client identifier".to_string())?;

        let local_connection_id = self
            .local_connection_id.as_ref()
            .ok_or_else(|| "missing local connection identifier".to_string())?;

        let remote_client_id = self
            .remote_client_id.as_ref()
            .ok_or_else(|| "missing remote client identifier".to_string())?;

        let remote_connection_id = self
            .remote_connection_id.as_ref()
            .ok_or_else(|| "missing remote connection identifier".to_string())?;

        let remote_cmt_prefix = CommitmentPrefix::new(remote_chain_config.store_prefix.as_bytes().to_vec());

        // TODO: Hardcode account for now. Figure out a way to retrieve the real account
        let address = "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C";
        let mut account: [u8; 20] = Default::default();
        account.copy_from_slice((&address[0..19]).as_ref());
        let signer = Id::new(account);

        let msg = MsgConnectionOpenInit::new(
            local_connection_id.to_string(),
            local_client_id.to_string(),
            remote_connection_id.to_string(),
            remote_client_id.to_string(),
            remote_cmt_prefix,
            signer
        );

        //TODO handle result better
        Ok((local_chain_config.clone(), msg.unwrap()))
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

        // Perform some message message validation
        match msg.validate_basic() {
            Ok(_) => {
                // Create chain
                let chain = CosmosSDKChain::from_config(chain_config).unwrap();

                // Build and sign transaction
                let _signed = chain.build_sign_tx(vec![Box::new(msg)]);

                // Send message
                // chain.send_msg()

            },
            Err(e) => status_info!("Error encountered on validating message:", "{}", e),
        }
    }
}
