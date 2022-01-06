//! Various packet encoding semantics which underpin the various types of transactions.

pub mod ics20_fungible_token_transfer;

// TODO: Move into its own directory
pub mod ics27_interchain_accounts {
    /// The port identifier that the ICS27 applications
    /// typically bind with. This is merely a prefix
    /// of the full port identifier, which has a
    /// complex structure.
    ///
    /// https://github.com/cosmos/ibc/tree/master/spec/app/ics-027-interchain-accounts#registering--controlling-flows
    pub const PORT_ID_PREFIX: &str = "ics27-1.";

    /// ICS27 application current version.
    pub const VERSION: &str = "ics27-1";
}
