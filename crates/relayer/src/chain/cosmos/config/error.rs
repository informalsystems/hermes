use flex_error::define_error;
use ibc_relayer_types::core::{
    ics02_client::trust_threshold::TrustThreshold,
    ics24_host::identifier::ChainId,
};

define_error! {
    Error {
        InvalidTrustThreshold
        {
            threshold: TrustThreshold,
            chain_id: ChainId,
            reason: String
        }
        |e| {
            format!("config file specifies an invalid `trust_threshold` ({0}) for the chain '{1}', caused by: {2}",
                e.threshold, e.chain_id, e.reason)
        },

        DeprecatedGasAdjustment
        {
            gas_adjustment: f64,
            gas_multiplier: f64,
            chain_id: ChainId,
        }
        |e| {
            format!(
                "config file specifies deprecated setting `gas_adjustment = {1}` for the chain '{0}'; \
                to get the same behavior, use `gas_multiplier = {2}",
                e.chain_id, e.gas_adjustment, e.gas_multiplier
            )
        },
    }
}
