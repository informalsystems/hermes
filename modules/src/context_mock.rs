use crate::context::{ChainKeeper, ChainReader, HistoricalInfo, SelfHeader};
use crate::mock_client::header::MockHeader;
use serde_derive::{Deserialize, Serialize};
use std::error::Error;
use tendermint::block::Height;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct MockChainContext {
    pub max_size: usize,
    pub latest: Height,
    pub history: Vec<HistoricalInfo>,
}

impl MockChainContext {
    pub fn new(max_size: usize, n: Height) -> Self {
        Self {
            max_size,
            latest: n,
            history: (0..n.value())
                .map(|i| HistoricalInfo {
                    header: SelfHeader::Mock(MockHeader(Height(i).increment())),
                })
                .collect(),
        }
    }

    pub fn max_size(&self) -> usize {
        self.max_size
    }

    /// Used for testing
    pub fn populate(&mut self, hs: Vec<u64>) {
        for h in hs {
            self.store_historical_info(
                Height(h),
                HistoricalInfo {
                    header: SelfHeader::Mock(MockHeader(Height(h))),
                },
            );
        }
    }

    /// Used for testing
    pub fn validate(&self) -> Result<(), Box<dyn Error>> {
        // check that the number of entries is not higher than max_size
        if self.history.len() > self.max_size {
            return Err("too many entries".to_string().into());
        }

        // check latest is properly updated with highest header height
        let SelfHeader::Mock(lh) = self.history[self.history.len() - 1].header;
        if lh.height() != self.latest {
            return Err("latest height is not updated".to_string().into());
        }

        // check that all headers are in sequential order
        for i in 1..self.history.len() {
            let SelfHeader::Mock(ph) = self.history[i - 1].header;
            let SelfHeader::Mock(h) = self.history[i].header;
            if ph.height().increment() != h.height() {
                return Err("headers in history not sequential".to_string().into());
            }
        }
        Ok(())
    }
}

impl ChainReader for MockChainContext {
    fn self_historical_info(&self, height: Height) -> Option<&HistoricalInfo> {
        let l = height.value() as usize;
        let h = self.latest.value() as usize;

        if l <= h - self.max_size {
            // header with height not in the history
            None
        } else {
            Some(&self.history[h - l])
        }
    }
}

impl ChainKeeper for MockChainContext {
    fn store_historical_info(&mut self, height: Height, info: HistoricalInfo) {
        if height != self.latest.increment() {
            return;
        }
        let mut history = self.history.clone();
        if history.len() >= self.max_size {
            history.rotate_left(1);
            history[self.max_size - 1] = info;
        } else {
            history.push(info);
        }
        //history.insert(height, info);
        self.history = history;
        self.latest = height;
    }
}

#[cfg(test)]
mod tests {
    use crate::context_mock::MockChainContext;
    use tendermint::block::Height;

    #[test]
    fn test_store_historical_info() {
        pub struct Test {
            name: String,
            ctx: MockChainContext,
            args: Vec<u64>,
        }

        impl Test {
            pub fn apply(&mut self, hs: Vec<u64>) {
                self.ctx.populate(hs);
            }
        }

        let tests: Vec<Test> = vec![
            Test {
                name: "Add no prune".to_string(),
                ctx: MockChainContext::new(3, Height(0)),
                args: [1].to_vec(),
            },
            Test {
                name: "Add with prune".to_string(),
                ctx: MockChainContext::new(3, Height(2)),
                args: [3, 4].to_vec(),
            },
            Test {
                name: "Attempt to add non sequential headers".to_string(),
                ctx: MockChainContext::new(3, Height(2)),
                args: [3, 5, 7].to_vec(),
            },
        ];

        for mut test in tests {
            test.apply(test.args.clone());
            assert!(test.ctx.validate().is_ok());
        }
    }
}
