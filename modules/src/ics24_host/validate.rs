use super::error::{ValidationError, ValidationKind};

/// Bails from the current function with the given error kind.
macro_rules! bail {
    ($kind:expr) => {
        return Err($kind.into());
    };
}

/// Path separator (ie. forward slash '/')
const PATH_SEPARATOR: char = '/';
const VALID_SPECIAL_CHARS: &str = "._+-#[]<>";

/// Default validator function for identifiers.
///
/// A valid identifier only contain lowercase alphabetic characters, and be of a given min and max
/// length.
pub fn validate_identifier(id: &str, min: usize, max: usize) -> Result<(), ValidationError> {
    assert!(max >= min);

    // Check identifier is not empty
    if id.is_empty() {
        bail!(ValidationKind::empty());
    }

    // Check identifier does not contain path separators
    if id.contains(PATH_SEPARATOR) {
        bail!(ValidationKind::contains_separator(id.to_string()));
    }

    // Check identifier length is between given min/max
    if id.len() < min || id.len() > max {
        bail!(ValidationKind::invalid_length(
            id.to_string(),
            id.len(),
            min,
            max
        ));
    }

    // Check that the identifier comprises only valid characters:
    // - Alphanumeric
    // - `.`, `_`, `+`, `-`, `#`
    // - `[`, `]`, `<`, `>`
    if !id
        .chars()
        .all(|c| c.is_alphanumeric() || VALID_SPECIAL_CHARS.contains(c))
    {
        bail!(ValidationKind::invalid_character(id.to_string()));
    }

    // All good!
    Ok(())
}

/// Default validator function for Client identifiers.
///
/// A valid identifier must be between 9-20 characters and only contain lowercase
/// alphabetic characters,
pub fn validate_client_identifier(id: &str) -> Result<(), ValidationError> {
    validate_identifier(id, 9, 20)
}

/// Default validator function for Connection identifiers.
///
/// A valid Identifier must be between 10-20 characters and only contain lowercase
/// alphabetic characters,
pub fn validate_connection_identifier(id: &str) -> Result<(), ValidationError> {
    validate_identifier(id, 10, 20)
}

/// Default validator function for Port identifiers.
///
/// A valid Identifier must be between 2-20 characters and only contain lowercase
/// alphabetic characters,
pub fn validate_port_identifier(id: &str) -> Result<(), ValidationError> {
    validate_identifier(id, 2, 20)
}

/// Default validator function for Channel identifiers.
///
/// A valid Identifier must be between 10-20 characters and only contain lowercase
/// alphabetic characters,
pub fn validate_channel_identifier(id: &str) -> Result<(), ValidationError> {
    validate_identifier(id, 10, 20)
}
