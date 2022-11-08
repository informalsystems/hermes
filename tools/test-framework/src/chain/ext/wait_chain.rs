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
        .query_latest_height()
        .ok()
        .unwrap();

    let start = SystemTime::now();
    while reference_application_latest_height < target_reference_application_height {
        // Check if the wait time has timed out.
        match SystemTime::now().duration_since(start) {
            Ok(elapsed_time) => {
                if elapsed_time > timeout_bound {
                    return Err(Error::generic(eyre!(
                        "chain did not reach desired height after {} seconds",
                        timeout_bound.as_secs()
                    )));
                }
            }
            Err(e) => {
                return Err(Error::generic(eyre!(
                    "error checking elapsed time in wait_for_chain_height: {}",
                    e
                )));
            }
        }
        std::thread::sleep(Duration::from_millis(500));

        // Query the latest height of the chain
        reference_application_latest_height = foreign_clients
            .client_a_to_b
            .src_chain()
            .query_latest_height()
            .ok()
            .unwrap();
    }
    Ok(())
}
