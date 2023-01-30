use core::fmt::{Debug, Display, Error as FmtError, Formatter};
use std::time::Duration;

use ibc_proto::{
    cosmos::tx::v1beta1::Fee,
    google::protobuf::Any,
    ibc::core::{
        channel::v1::{Counterparty as ChannelCounterparty, IdentifiedChannel},
        client::v1::{ConsensusStateWithHeight, Height, IdentifiedClientState},
        connection::v1::{Counterparty as ConnectionCounterparty, IdentifiedConnection, Version},
    },
};
use tendermint::abci::Code;

use crate::event::IbcEventWithHeight;

pub struct PrettyAny<'a>(pub &'a Any);

impl<'a> Display for PrettyAny<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "Any {{ type_url: {} }}", self.0.type_url)
    }
}

pub struct PrettyChannelCounterparty<'a>(pub &'a ChannelCounterparty);

impl Display for PrettyChannelCounterparty<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(
            f,
            "Counterparty {{ channel_id: {}, port_id: {} }}",
            self.0.channel_id, self.0.port_id
        )
    }
}

pub struct PrettyCode<'a>(pub &'a Code);

impl Display for PrettyCode<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match &self.0 {
            Code::Ok => write!(f, "Ok"),
            Code::Err(code) => write!(f, "Error with code {code}"),
        }
    }
}

pub struct PrettyConnectionCounterparty<'a>(pub &'a ConnectionCounterparty);

impl Display for PrettyConnectionCounterparty<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(
            f,
            "Counterparty {{ connection_id: {}, client_id: {} }}",
            self.0.connection_id, self.0.client_id
        )
    }
}

pub struct PrettyConsensusStateWithHeight<'a>(pub &'a ConsensusStateWithHeight);

impl Display for PrettyConsensusStateWithHeight<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match (&self.0.height, &self.0.consensus_state) {
            (Some(height), Some(consensus_state)) => write!(
                f,
                "ConsensusStateWithHeight {{ height: {}, consensus_state: {} }}",
                PrettyHeight(height),
                PrettyAny(consensus_state)
            ),
            (Some(height), None) => write!(
                f,
                "ConsensusStateWithHeight {{ height: {}, consensus_state: None }}",
                PrettyHeight(height)
            ),
            (None, Some(consensus_state)) => write!(
                f,
                "ConsensusStateWithHeight {{ height: None, consensus_state: {} }}",
                PrettyAny(consensus_state)
            ),
            (None, None) => write!(
                f,
                "ConsensusStateWithHeight {{ height: None, consensus_state: None }}"
            ),
        }
    }
}

pub struct PrettyDuration<'a>(pub &'a Duration);

impl Display for PrettyDuration<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        Debug::fmt(self.0, f)
    }
}

/// For use in debug messages
pub struct PrettyEvents<'a>(pub &'a [IbcEventWithHeight]);

impl<'a> Display for PrettyEvents<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        writeln!(f, "events:")?;
        for v in self.0 {
            writeln!(f, "\t{v}")?;
        }
        Ok(())
    }
}

pub struct PrettyFee<'a>(pub &'a Fee);

impl Display for PrettyFee<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        let amount = match self.0.amount.get(0) {
            Some(coin) => format!("{}{}", coin.amount, coin.denom),
            None => "<no amount specified>".to_string(),
        };

        f.debug_struct("Fee")
            .field("amount", &amount)
            .field("gas_limit", &self.0.gas_limit)
            .finish()
    }
}

pub struct PrettyHeight<'a>(pub &'a Height);

impl Display for PrettyHeight<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(
            f,
            "Height {{ revision_number: {}, revision_height: {} }}",
            self.0.revision_number, self.0.revision_height
        )
    }
}

pub struct PrettyIdentifiedClientState<'a>(pub &'a IdentifiedClientState);

impl Display for PrettyIdentifiedClientState<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match &self.0.client_state {
            Some(client_state) => write!(
                f,
                "IdentifiedClientState {{ client_id: {}, client_state: {} }}",
                self.0.client_id,
                PrettyAny(client_state)
            ),
            None => write!(
                f,
                "IdentifiedClientState {{ client_id: {}, client_state: None }}",
                self.0.client_id
            ),
        }
    }
}

pub struct PrettyIdentifiedChannel<'a>(pub &'a IdentifiedChannel);

impl Display for PrettyIdentifiedChannel<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match &self.0.counterparty {
            Some(counterparty) => write!(f, "IdentifiedChannel {{ state: {}, ordering: {}, counterparty: {}, connection_hops: {}, version: {}, port_id: {}, channel_id: {} }}", self.0.state, self.0.ordering, PrettyChannelCounterparty(counterparty), PrettySlice(&self.0.connection_hops), self.0.version, self.0.port_id, self.0.channel_id),
            None => write!(f, "IdentifiedChannel {{ state: {}, ordering: {}, counterparty: None, connection_hops: {}, version: {}, port_id: {}, channel_id: {} }}", self.0.state, self.0.ordering, PrettySlice(&self.0.connection_hops), self.0.version, self.0.port_id, self.0.channel_id),
        }
    }
}

pub struct PrettyIdentifiedConnection<'a>(pub &'a IdentifiedConnection);

impl Display for PrettyIdentifiedConnection<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        let versions: Vec<PrettyVersion<'_>> = self.0.versions.iter().map(PrettyVersion).collect();
        match &self.0.counterparty {
            Some(counterparty) => write!(f, "IdentifiedConnection {{ id: {}, client_id: {}, versions: {}, state: {}, counterparty: {}, delay_period: {} }}", self.0.id, self.0.client_id, PrettySlice(&versions), self.0.state, PrettyConnectionCounterparty(counterparty), self.0.delay_period),
            None => write!(f, "IdentifiedConnection {{ id: {}, client_id: {}, versions: {}, state: {}, counterparty: None, delay_period: {} }}", self.0.id, self.0.client_id, PrettySlice(&versions), self.0.state, self.0.delay_period),
        }
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

pub struct PrettyVersion<'a>(pub &'a Version);

impl Display for PrettyVersion<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "Version {{ identifier: {} }}", self.0.identifier)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pretty_code_ok() {
        let expected_output = "Ok";

        let code = Code::from(0);
        let pretty_code = PrettyCode(&code);

        assert_eq!(pretty_code.to_string(), expected_output);
    }

    #[test]
    fn test_pretty_code_err() {
        let expected_output = "Error with code 10";

        let code = Code::from(10);
        let pretty_code = PrettyCode(&code);

        assert_eq!(pretty_code.to_string(), expected_output);
    }

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
