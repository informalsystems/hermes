use core::time::Duration;

use http::uri::Uri;
use ibc_proto::cosmos::tx::v1beta1::Fee;
use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::cosmos::types::account::AccountNumber;
use ibc_relayer::chain::cosmos::types::gas::GasConfig;
use ibc_relayer::config::types::Memo;
use ibc_relayer::config::AddressType;
use ibc_relayer::keyring::Secp256k1KeyPair;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use tendermint_rpc::{HttpClient, Url};

pub trait HasKeyEntry {
    fn key_entry(&self) -> &Secp256k1KeyPair;
}

pub trait HasAccountNumber {
    fn account_number(&self) -> &AccountNumber;
}

pub trait HasAddressType {
    fn address_type(&self) -> &AddressType;
}

pub trait HasMemo {
    fn memo(&self) -> &Memo;
}

pub trait HasExtensionOptions {
    fn extension_options(&self) -> &Vec<Any>;
}

pub trait HasChainId {
    fn chain_id(&self) -> &ChainId;
}

pub trait HasRpcClient {
    fn rpc_client(&self) -> &HttpClient;
}

pub trait HasRpcAddress {
    fn rpc_address(&self) -> &Url;
}

pub trait HasGrpcAddress {
    fn grpc_address(&self) -> &Uri;
}

pub trait HasGasConfig {
    fn gas_config(&self) -> &GasConfig;
}

pub trait HasDefaultGas {
    fn default_gas(&self) -> u64;
}

pub trait HasMaxGas {
    fn max_gas(&self) -> u64;
}

pub trait HasMaxFee {
    fn max_fee(&self) -> Fee;
}

pub trait HasWaitTimeout {
    fn wait_timeout(&self) -> &Duration;

    fn wait_backoff(&self) -> &Duration;
}
