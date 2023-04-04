use core::str::FromStr;
use core::time::Duration;

use http::uri::Uri;

use ibc_proto::cosmos::tx::v1beta1::Fee;
use ibc_relayer::chain::cosmos::gas::calculate_fee;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::cosmos::types::gas::GasConfig;
use ibc_relayer::config::{AddressType, GasPrice};
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use tendermint_rpc::Url;

use crate::error::{handle_generic_error, Error};

pub fn gas_config_for_test() -> GasConfig {
    let max_gas = 3000000;
    let gas_multiplier = 1.1;
    let gas_price = GasPrice::new(0.003, "stake".to_string());

    let default_gas = max_gas;
    let fee_granter = "".to_string();

    let max_fee = Fee {
        amount: vec![calculate_fee(max_gas, &gas_price)],
        gas_limit: max_gas,
        payer: "".to_string(),
        granter: fee_granter.clone(),
    };

    GasConfig {
        default_gas,
        max_gas,
        gas_multiplier,
        gas_price,
        max_fee,
        fee_granter,
    }
}

pub fn new_tx_config_for_test(
    chain_id: ChainId,
    raw_rpc_address: String,
    raw_grpc_address: String,
    address_type: AddressType,
) -> Result<TxConfig, Error> {
    let rpc_address = Url::from_str(&raw_rpc_address).map_err(handle_generic_error)?;
    let grpc_address = Uri::from_str(&raw_grpc_address).map_err(handle_generic_error)?;
    let gas_config = gas_config_for_test();
    let rpc_timeout = Duration::from_secs(30);
    let max_msg_num = Default::default();
    let max_tx_size = Default::default();
    let extension_options = Default::default();

    Ok(TxConfig {
        chain_id,
        gas_config,
        rpc_address,
        grpc_address,
        rpc_timeout,
        address_type,
        max_msg_num,
        max_tx_size,
        extension_options,
    })
}
