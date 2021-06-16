use flex_error::*;

define_error! {
    ValidationError {
        ContainSeparator
            {id : String }
            | e | { format_args!("identifier {0} cannot contain separator '/'", e.id) },

        InvalidLength
            {
                id: String,
                length: usize,
                min: usize,
                max: usize,
            }
            | e | { format_args!("identifier {0} has invalid length {1} must be between {2}-{3} characters", e.id, e.length, e.min, e.max) },

        InvalidCharacter
            { id: String }
            | e | { format_args!("identifier {0} must only contain alphanumeric characters or `.`, `_`, `+`, `-`, `#`, - `[`, `]`, `<`, `>`", e.id) },

        Empty
            | _ | { "identifier cannot be empty" },

        ChainIdInvalidFormat
            { id: String }
            | e | { format_args!("chain identifiers are expected to be in epoch format {0}", e.id) },

        InvalidCounterpartyChannelId
            |_| { "Invalid channel id in counterparty" }
    }
}

// #[derive(Clone, Debug, Display, PartialEq, Eq)]
// pub enum ValidationKind {
//     /// identifier {id} cannot contain separator '/'
//     ContainsSeparator { id: String },
//
//     /// identifier {id} has invalid length {length} must be between {min}-{max} characters
//     InvalidLength {
//         id: String,
//         length: usize,
//         min: usize,
//         max: usize,
//     },
//
//     /// identifier {id} must only contain alphanumeric characters or `.`, `_`, `+`, `-`, `#`, - `[`, `]`, `<`, `>`
//     InvalidCharacter { id: String },
//
//     /// identifier cannot be empty
//     Empty,
//
//     /// chain identifiers are expected to be in epoch format {id}
//     ChainIdInvalidFormat { id: String },
//
//     /// Invalid channel id in counterparty
//     InvalidCounterpartyChannelId,
// }
//
// impl ValidationKind {
//     pub fn contains_separator(id: String) -> Self {
//         Self::ContainsSeparator { id }
//     }
//
//     pub fn invalid_length(id: String, length: usize, min: usize, max: usize) -> Self {
//         Self::InvalidLength {
//             id,
//             length,
//             min,
//             max,
//         }
//     }
//
//     pub fn invalid_character(id: String) -> Self {
//         Self::InvalidCharacter { id }
//     }
//
//     pub fn empty() -> Self {
//         Self::Empty
//     }
//
//     pub fn chain_id_invalid_format(id: String) -> Self {
//         Self::ChainIdInvalidFormat { id }
//     }
//
//     pub fn kind(&self) -> &Self {
//         &self
//     }
//
// }
