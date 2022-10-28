use crate::base::chain::traits::queries::status::CanQueryChainStatus;
use crate::verification::mock::{ChainStatus, MockChain};

/**
   A very basic test to test the model checking capabilities of Kani.
*/

#[kani::proof]
#[kani::unwind(10)]
async fn test_kani() {
    let height: u64 = kani::any();
    kani::assume(height < 8);

    let timestamp: u64 = kani::any();

    let mut chain = MockChain {
        current_status: ChainStatus { height, timestamp },
    };

    for _ in 0..5 {
        chain.current_status.height += 1;
        let status = chain.query_chain_status().await.unwrap();

        // This is expected to fail
        assert!(status.height < 10);
    }
}
