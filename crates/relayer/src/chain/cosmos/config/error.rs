use flex_error::define_error;
use flex_error::TraceError;

use ibc_relayer_types::core::ics02_client::trust_threshold::TrustThreshold;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;

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

        ExpectedExcludedSequencesArray
        |_| { "expected excluded_sequences to be an array of values" },

        InvalidExcludedSequencesSeparator
        { separator: String }
        |e| {
            format!("excluded_sequences range `{}` is invalid, only '..', '..=' and '-' are valid separators", e.separator)
        },

        MissingStartExcludedSequence
        { entry: String }
        |e| {
            format!("missing the excluded sequence value before the separator in the entry `{}`", e.entry)
        },

        MissingEndExcludedSequence
        { entry: String }
        |e| {
            format!("missing the excluded sequence value after the separator in the entry `{}`", e.entry)
        },

        ParsingStartExcludedSequenceFailed
        { entry: String }
        [ TraceError<std::num::ParseIntError> ]
        |e| {
            format!("Error parsing starting sequence as integer in entry `{}`", e.entry)
        },


        ParsingEndExcludedSequenceFailed
        { entry: String }
        [ TraceError<std::num::ParseIntError> ]
        |e| {
            format!("Error parsing ending sequence as integer in entry `{}`", e.entry)
        },
    }
}
