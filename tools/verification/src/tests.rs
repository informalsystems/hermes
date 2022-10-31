use ibc_relayer_framework::base::chain::traits::queries::status::CanQueryChainStatus;

use crate::future::poll_future;
use crate::mock::{ChainStatus, MockChain, Natural};
use crate::std_prelude::*;

/**
   A very basic test to test the model checking capabilities of Kani.
*/

#[kani::proof]
#[kani::unwind(10)]
async fn test_kani() {
    let init_height: Natural = kani::any();
    let init_timestamp: Natural = kani::any();

    let mut chain = MockChain {
        current_status: ChainStatus {
            height: init_height,
            timestamp: init_timestamp,
        },
    };

    // If we do not check the chain's current height before
    // incrementing, this would result in an error from Kani
    if chain.current_status.height < Natural::MAX {
        chain.current_status.height += 1;

        let mut future = chain.query_chain_status();

        // MVP that we can poll future result manually inside Kani
        let status = poll_future(&mut future).unwrap().unwrap();

        assert_eq!(status.height, chain.current_status.height);
    }
}
