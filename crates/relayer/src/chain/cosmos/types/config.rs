use core::str::FromStr;
use core::time::Duration;
use http::Uri;
use ibc_proto::google::protobuf::Any;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use tendermint_rpc::{HttpClient, Url};

use crate::chain::cosmos::types::gas::GasConfig;
use crate::config::types::{MaxMsgNum, MaxTxSize};
use crate::config::{AddressType, ChainConfig};
use crate::error::Error;

#[derive(Debug, Clone)]
pub struct TxConfig {
    pub chain_id: ChainId,
    pub gas_config: GasConfig,
    pub rpc_client: HttpClient,
    pub rpc_address: Url,
    pub grpc_address: Uri,
    pub rpc_timeout: Duration,
    pub address_type: AddressType,
    pub max_msg_num: MaxMsgNum,
    pub max_tx_size: MaxTxSize,
    pub extension_options: Vec<Any>,
}

impl<'a> TryFrom<&'a ChainConfig> for TxConfig {
    type Error = Error;

    fn try_from(config: &'a ChainConfig) -> Result<Self, Error> {
        let rpc_client = HttpClient::new(config.rpc_addr.clone())
            .map_err(|e| Error::rpc(config.rpc_addr.clone(), e))?;

        let grpc_address = Uri::from_str(&config.grpc_addr.to_string())
            .map_err(|e| Error::invalid_uri(config.grpc_addr.to_string(), e))?;

        let gas_config = GasConfig::from(config);

        let extension_options = config
            .extension_options
            .iter()
            .map(|opt| opt.to_any())
            .collect::<Result<_, _>>()?;

        Ok(Self {
            chain_id: config.id.clone(),
            gas_config,
            rpc_client,
            rpc_address: config.rpc_addr.clone(),
            grpc_address,
            rpc_timeout: config.rpc_timeout,
            address_type: config.address_type.clone(),
            max_msg_num: config.max_msg_num,
            max_tx_size: config.max_tx_size,
            extension_options,
        })
    }
}
