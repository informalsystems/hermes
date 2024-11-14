use core::fmt;
use std::ops::Div;
use std::str::FromStr;

use serde::Deserialize;
use subtle_encoding::base64;
use tendermint_rpc::Url;
use tracing::{debug, trace};

use ibc_proto::cosmos::base::v1beta1::{DecCoin, DecProto};
use ibc_relayer_types::core::ics24_host::identifier::ChainId;

use crate::error::Error;

pub async fn query_eip_base_fee(
    rpc_address: &Url,
    gas_price_denom: &str,
    chain_id: &ChainId,
) -> Result<f64, Error> {
    debug!("Querying Omosis EIP-1559 base fee from {rpc_address}");

    let chain_name = chain_id.name();

    let is_osmosis = chain_name.starts_with("osmosis") || chain_name.starts_with("osmo-test");

    let url = if is_osmosis {
        format!(
            "{}abci_query?path=\"/osmosis.txfees.v1beta1.Query/GetEipBaseFee\"",
            rpc_address
        )
    } else {
        format!(
            "{}abci_query?path=\"/feemarket.feemarket.v1.Query/GasPrices\"&denom={}",
            rpc_address, gas_price_denom
        )
    };

    let response = reqwest::get(&url).await.map_err(Error::http_request)?;

    if !response.status().is_success() {
        return Err(Error::http_response(response.status()));
    }

    #[derive(Deserialize)]
    struct EipBaseFeeHTTPResult {
        result: EipBaseFeeResult,
    }

    #[derive(Deserialize)]
    struct EipBaseFeeResult {
        response: EipBaseFeeResponse,
    }

    #[derive(Deserialize)]
    struct EipBaseFeeResponse {
        value: String,
    }

    let result: EipBaseFeeHTTPResult = response.json().await.map_err(Error::http_response_body)?;

    let amount = if is_osmosis {
        extract_dynamic_gas_price_osmosis(result.result.response.value)?
    } else {
        extract_dynamic_gas_price(result.result.response.value)?
    };

    trace!("EIP-1559 base fee: {amount}");

    Ok(amount)
}

/// This method extracts the gas base fee from Skip's feemarket
fn extract_dynamic_gas_price(encoded: String) -> Result<f64, Error> {
    let decoded = base64::decode(encoded).map_err(Error::base64_decode)?;

    let gas_price_response: GasPriceResponse =
        prost::Message::decode(decoded.as_ref()).map_err(|e| {
            Error::protobuf_decode("feemarket.feemarket.v1.GasPricesResponse".to_string(), e)
        })?;
    let dec_coin = gas_price_response.price.unwrap().clone();
    let base_fee_uint128 = Uint128::from_str(&dec_coin.amount).map_err(Error::parse_int)?;

    let dec = Decimal::new(base_fee_uint128);
    f64::from_str(dec.to_string().as_str()).map_err(Error::parse_float)
}

/// This method extracts the gas base fee from Osmosis EIP-1559
fn extract_dynamic_gas_price_osmosis(encoded: String) -> Result<f64, Error> {
    let decoded = base64::decode(encoded).map_err(Error::base64_decode)?;

    let dec_proto: DecProto = prost::Message::decode(decoded.as_ref())
        .map_err(|e| Error::protobuf_decode("cosmos.base.v1beta1.DecProto".to_string(), e))?;

    let base_fee_uint128 = Uint128::from_str(&dec_proto.dec).map_err(Error::parse_int)?;

    let dec = Decimal::new(base_fee_uint128);
    f64::from_str(dec.to_string().as_str()).map_err(Error::parse_float)
}

/// GasPriceResponse is the response type for the Query/GasPrice RPC method.
/// Returns a gas price in specified denom.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct GasPriceResponse {
    #[prost(message, optional, tag = "1")]
    pub price: ::core::option::Option<DecCoin>,
}

/// Extracted from `cosmwasm-std`
///
/// <https://docs.rs/cosmwasm-std/latest/src/cosmwasm_std/math/uint128.rs.html>
#[derive(Clone, Copy)]
struct Uint128(u128);

impl Uint128 {
    pub const fn new(value: u128) -> Self {
        Self(value)
    }

    pub fn is_zero(&self) -> bool {
        self.0 == 0
    }

    pub fn checked_rem(&self, rhs: Self) -> Option<Self> {
        self.0.checked_rem(rhs.0).map(Self)
    }
}

impl FromStr for Uint128 {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse::<u128>().map(Self)
    }
}

impl Div<Uint128> for Uint128 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        Self(
            self.0
                .checked_div(rhs.0)
                .expect("attempt to divide by zero"),
        )
    }
}

impl fmt::Display for Uint128 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// Extracted from `cosmwasm-std`
///
/// <https://docs.rs/cosmwasm-std/latest/src/cosmwasm_std/math/decimal.rs.html>
#[derive(Clone, Copy)]
struct Decimal(Uint128);

impl Decimal {
    const DECIMAL_FRACTIONAL: Uint128 = Uint128::new(1_000_000_000_000_000_000u128); // 1*10**18
    pub const DECIMAL_PLACES: u32 = 18;

    pub const fn new(value: Uint128) -> Self {
        Self(value)
    }
}

impl fmt::Display for Decimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use core::fmt::Write;

        let whole = (self.0) / Self::DECIMAL_FRACTIONAL;
        let fractional = (self.0).checked_rem(Self::DECIMAL_FRACTIONAL).unwrap();

        if fractional.is_zero() {
            write!(f, "{whole}")
        } else {
            let fractional_string = format!(
                "{:0>padding$}",
                fractional,
                padding = Self::DECIMAL_PLACES as usize
            );
            f.write_str(&whole.to_string())?;
            f.write_char('.')?;
            f.write_str(fractional_string.trim_end_matches('0'))?;
            Ok(())
        }
    }
}
