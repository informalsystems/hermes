use core::str::FromStr;
use eyre::eyre;
use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;
use serde_json as json;
use tracing::info;

use crate::bootstrap::deployment::ChainDeployment;
use crate::bootstrap::pair::boostrap_chain_pair;
use crate::chain::builder::ChainBuilder;
use crate::error::Error;
use crate::ibc::denom::derive_ibc_denom;
use crate::init::init_test;
use crate::relayer::channel::{bootstrap_channel, Channel};
use crate::tagged::*;
use crate::util::random::random_u64_range;

#[test]
fn test_memo() -> Result<(), Error> {
    Ok(())
}
