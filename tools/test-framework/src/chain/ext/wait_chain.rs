use std::time::SystemTime;

use ibc_relayer_types::core::ics02_client::height::Height;

use crate::prelude::*;

/// Wait for a chain to get to a desired height, and timeout if
/// the chain didn't get to that height in the desired amount of
/// time.
pub fn wait_for_chain_height<ChainA: ChainHandle, ChainB: ChainHandle>(
    foreign_clients: &ForeignClientPair<ChainA, ChainB>,
    target_height_of_a: Height,
    timeout_bound: Duration,
) -> Result<(), Error> {
    // Query the latest height of the chain
    let mut reference_application_latest_height = foreign_clients
        .client_a_to_b
        .src_chain()
        .query_latest_height()?;

    let start = SystemTime::now();
    while reference_application_latest_height < target_height_of_a {
        // Check if the wait time has timed out.
        let elapsed_time = SystemTime::now()
            .duration_since(start)
            .map_err(handle_generic_error)?;

        if elapsed_time > timeout_bound {
            return Err(Error::generic(eyre!(
                "chain did not reach desired height after {} seconds",
                timeout_bound.as_secs()
            )));
        }
        std::thread::sleep(Duration::from_millis(500));

        // Query the latest height of the chain
        reference_application_latest_height = foreign_clients
            .client_a_to_b
            .src_chain()
            .query_latest_height()?;
    }
    Ok(())
}
