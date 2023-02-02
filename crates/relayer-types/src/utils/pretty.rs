use core::fmt::{Debug, Display, Error as FmtError, Formatter};
use core::time::Duration;
use tendermint::block::signed_header::SignedHeader;
use tendermint::validator::Set as ValidatorSet;

use alloc::vec::Vec;

pub struct PrettyDuration<'a>(pub &'a Duration);

impl Display for PrettyDuration<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        Debug::fmt(self.0, f)
    }
}

pub struct PrettyOption<'a, T>(pub &'a Option<T>);

impl<'a, T: Display> Display for PrettyOption<'a, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match &self.0 {
            Some(v) => write!(f, "{v}"),
            None => write!(f, "None"),
        }
    }
}

pub struct PrettySignedHeader<'a>(pub &'a SignedHeader);

impl Display for PrettySignedHeader<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(
            f,
            "SignedHeader {{ header: {{ chain_id: {}, height: {} }}, commit: {{ height: {} }} }}",
            self.0.header.chain_id, self.0.header.height, self.0.commit.height
        )
    }
}

pub struct PrettyValidatorSet<'a>(pub &'a ValidatorSet);

impl Display for PrettyValidatorSet<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        let validator_addresses: Vec<_> = self
            .0
            .validators()
            .iter()
            .map(|validator| validator.address)
            .collect();
        if let Some(proposer) = self.0.proposer() {
            match &proposer.name {
                Some(name) => write!(f, "PrettyValidatorSet {{ validators: {}, proposer: {}, total_voting_power: {} }}", PrettySlice(&validator_addresses), name, self.0.total_voting_power()),
                None =>  write!(f, "PrettyValidatorSet {{ validators: {}, proposer: None, total_voting_power: {} }}", PrettySlice(&validator_addresses), self.0.total_voting_power()),
            }
        } else {
            write!(
                f,
                "PrettyValidatorSet {{ validators: {}, proposer: None, total_voting_power: {} }}",
                PrettySlice(&validator_addresses),
                self.0.total_voting_power()
            )
        }
    }
}

pub struct PrettySlice<'a, T>(pub &'a [T]);

impl<'a, T: Display> Display for PrettySlice<'a, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "[ ")?;
        let mut vec_iterator = self.0.iter().peekable();
        while let Some(element) = vec_iterator.next() {
            write!(f, "{element}")?;
            // If it is not the last element, add separator.
            if vec_iterator.peek().is_some() {
                write!(f, ", ")?;
            }
        }
        write!(f, " ]")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::alloc::string::ToString;
    use std::{string::String, vec};

    #[test]
    fn test_pretty_duration_micros() {
        let expected_output = "5µs";

        let duration = Duration::from_micros(5);
        let pretty_duration = PrettyDuration(&duration);

        assert_eq!(pretty_duration.to_string(), expected_output);
    }

    #[test]
    fn test_pretty_duration_millis() {
        let expected_output = "5ms";

        let duration = Duration::from_millis(5);
        let pretty_duration = PrettyDuration(&duration);

        assert_eq!(pretty_duration.to_string(), expected_output);
    }

    #[test]
    fn test_pretty_duration_secs() {
        let expected_output = "10s";

        let duration = Duration::from_secs(10);
        let pretty_duration = PrettyDuration(&duration);

        assert_eq!(pretty_duration.to_string(), expected_output);
    }

    #[test]
    fn test_pretty_option_some() {
        let expected_output = "Option content";

        let option_string = Some(String::from("Option content"));
        let pretty_option = PrettyOption(&option_string);

        assert_eq!(pretty_option.to_string(), expected_output);
    }

    #[test]
    fn test_pretty_option_none() {
        let expected_output = "None";

        let option_string: Option<String> = None;
        let pretty_option = PrettyOption(&option_string);

        assert_eq!(pretty_option.to_string(), expected_output);
    }

    #[test]
    fn test_pretty_vec_display() {
        let expected_output = "[ one, two, three ]";

        let string_vec = vec!["one", "two", "three"];
        let pretty_vec = PrettySlice(&string_vec);

        assert_eq!(pretty_vec.to_string(), expected_output);
    }

    #[test]
    fn test_pretty_vec_empty_vec() {
        let expected_output = "[  ]";

        let string_vec: Vec<String> = vec![];
        let pretty_vec = PrettySlice(&string_vec);

        assert_eq!(pretty_vec.to_string(), expected_output);
    }

    #[test]
    fn test_pretty_vec_single_element() {
        let expected_output = "[ one ]";

        let string_vec = vec!["one"];
        let pretty_vec = PrettySlice(&string_vec);

        assert_eq!(pretty_vec.to_string(), expected_output);
    }
}
