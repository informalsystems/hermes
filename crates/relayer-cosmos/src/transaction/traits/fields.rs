use http::uri::Uri;
use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::cosmos::types::account::{AccountNumber, AccountSequence};
use ibc_relayer::chain::cosmos::types::gas::GasConfig;
use ibc_relayer::config::types::Memo;
use ibc_relayer::config::AddressType;
use ibc_relayer::keyring::KeyEntry;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use tendermint_rpc::{HttpClient, Url};

pub trait HasKeyEntry {
    fn key_entry(&self) -> &KeyEntry;
}

pub trait HasAccountSequence {
    fn account_sequence(&self) -> &AccountSequence;
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
    fn rpc_address(&self) -> Url;
}

pub trait HasGrpcAddress {
    fn grpc_address(&self) -> Uri;
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
