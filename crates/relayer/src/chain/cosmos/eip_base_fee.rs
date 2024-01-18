use core::fmt;
use std::ops::Div;
use std::str::FromStr;

use tracing::info;

use crate::error::Error;

pub async fn query_eip_base_fee(rpc_address: &str) -> Result<f64, Error> {
    info!("Querying Omosis EIP-1559 base fee from {}", rpc_address);

    let url = format!(
        "{}/abci_query?path=\"/osmosis.txfees.v1beta1.Query/GetEipBaseFee\"",
        rpc_address
    );

    let response = reqwest::get(&url).await.map_err(Error::http_request)?;

    if !response.status().is_success() {
        return Err(Error::http_response(response.status()));
    }

    let body = response.text().await.map_err(Error::http_response_body)?;
    let json: serde_json::Value = serde_json::from_str(&body).map_err(Error::json_deserialize)?;
    let base_fee_encoded = json["result"]["response"]["value"]
        .as_str()
        .ok_or_else(|| Error::json_field("value".to_string()))?
        .to_string();

    let base_fee_decoded = subtle_encoding::base64::decode(base_fee_encoded).unwrap();

    let base_fee_dec_proto: DecProto = prost::Message::decode(base_fee_decoded.as_ref())
        .map_err(|_| Error::json_field("test".to_string()))?;

    let base_fee_uint128 = Uint128::from_str(&base_fee_dec_proto.dec)
        .map_err(|_| Error::json_field("test".to_string()))?;

    let base_fee_dec = Decimal::new(base_fee_uint128);

    let base_fee = f64::from_str(base_fee_dec.to_string().as_str()).unwrap();

    info!("Omosis EIP-1559 base fee is {}", base_fee);

    Ok(base_fee)
}

/// Extracted from `osmosis-std`
///
/// <https://docs.rs/osmosis-std/latest/osmosis_std/types/cosmos/base/v1beta1/struct.DecProto.html>
#[derive(prost::Message)]
pub struct DecProto {
    #[prost(string, tag = "1")]
    pub dec: String,
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
