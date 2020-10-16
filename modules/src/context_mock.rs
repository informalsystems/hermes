use std::cmp::min;
use std::error::Error;

use serde_derive::{Deserialize, Serialize};

use crate::context::{ChainKeeper, ChainReader, HistoricalInfo, SelfHeader};
use crate::ics02_client::client_def::{AnyConsensusState, AnyHeader};
use crate::ics02_client::height::{chain_version, Height};
use crate::mock_client::header::MockHeader;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, Default)]
pub struct MockChainContext {
    /// Chain identifier in the form <chain>-<version>
    pub chain_id: String,
    /// Maximum size of the history
    pub max_size: usize,
    /// Highest height of the headers in the history
    pub latest: Height,
    /// A list of `max_size` headers ordered by height
    pub history: Vec<MockHeader>,
}

impl MockChainContext {
    /// Creates a new mock chain with max_size number of headers up to height h
    pub fn new(chain_id: String, max_size: usize, h: Height) -> Self {
        // number of headers to store, if h is 0 nothing is stored
        let n = min(max_size as u64, h.version_height);
        Self {
            chain_id,
            max_size,
            latest: h,
            history: (0..n)
                .rev()
                .map(|i| MockHeader(Height::new(h.version_number, h.version_height - i)))
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
                Height {
                    version_number: 0,
                    version_height: h,
                },
                HistoricalInfo {
                    header: SelfHeader::Mock(MockHeader(Height {
                        version_number: 0,
                        version_height: h,
                    })),
                },
            );
        }
    }

    pub fn add_header(&mut self, h: u64) {
        let mut new_h = Height::new(chain_version(self.chain_id.clone()), h);
        if h == 0 {
            new_h.version_height = self.latest.version_height + 1;
        }
        self.store_historical_info(
            new_h,
            HistoricalInfo {
                header: SelfHeader::Mock(MockHeader(new_h)),
            },
        );
    }

    pub fn validate(&self) -> Result<(), Box<dyn Error>> {
        // check that the number of entries is not higher than max_size
        if self.history.len() > self.max_size {
            return Err("too many entries".to_string().into());
        }

        // get the highers header
        let lh = self.history[self.history.len() - 1];
        // check latest is properly updated with highest header height
        if lh.height() != self.latest {
            return Err("latest height is not updated".to_string().into());
        }

        // check that all headers are in sequential order
        for i in 1..self.history.len() {
            let ph = self.history[i - 1];
            let h = self.history[i];
            if ph.height().increment() != h.height() {
                return Err("headers in history not sequential".to_string().into());
            }
        }
        Ok(())
    }
}

impl ChainReader for MockChainContext {
    fn self_historical_info(&self, height: Height) -> Option<HistoricalInfo> {
        let l = height.version_height as usize;
        let h = self.latest.version_height as usize;

        if l <= h - self.max_size {
            // header with height not in the history
            None
        } else {
            Some(HistoricalInfo {
                header: SelfHeader::Mock(self.history[self.max_size + l - h - 1]),
            })
        }
    }

    fn header(&self, height: Height) -> Option<AnyHeader> {
        let hi = self.self_historical_info(height)?.header;
        match hi {
            #[cfg(test)]
            SelfHeader::Mock(h) => Some(h.into()),
            _ => None,
        }
    }

    fn fetch_self_consensus_state(&self, height: Height) -> Option<AnyConsensusState> {
        let hi = self.self_historical_info(height)?.header;
        match hi {
            #[cfg(test)]
            SelfHeader::Mock(h) => Some(h.into()),
            _ => None,
        }
    }
}

impl ChainKeeper for MockChainContext {
    fn store_historical_info(&mut self, height: Height, info: HistoricalInfo) {
        if height != self.latest.increment() {
            return;
        }
        if let SelfHeader::Mock(header) = info.header {
            let mut history = self.history.clone();
            if history.len() >= self.max_size {
                history.rotate_left(1);
                history[self.max_size - 1] = header;
            } else {
                history.push(header);
            }
            self.history = history;
            self.latest = height;
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::context_mock::MockChainContext;
    use crate::ics02_client::height::{chain_version, Height};

    #[test]
    fn test_store_historical_info() {
        let chain_id = "testchain-0".to_string();
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

        let chain_version = chain_version(chain_id.clone());
        let tests: Vec<Test> = vec![
            Test {
                name: "Add no prune".to_string(),
                ctx: MockChainContext::new(chain_id.clone(), 3, Height::new(chain_version, 0)),
                args: [1].to_vec(),
            },
            Test {
                name: "Add with prune".to_string(),
                ctx: MockChainContext::new(chain_id.clone(), 3, Height::new(chain_version, 2)),
                args: [3, 4].to_vec(),
            },
            Test {
                name: "Add with initial prune".to_string(),
                ctx: MockChainContext::new(chain_id.clone(), 3, Height::new(chain_version, 10)),
                args: [11].to_vec(),
            },
            Test {
                name: "Attempt to add non sequential headers".to_string(),
                ctx: MockChainContext::new(chain_id, 3, Height::new(chain_version, 2)),
                args: [3, 5, 7].to_vec(),
            },
        ];

        for mut test in tests {
            test.apply(test.args.clone());
            assert!(test.ctx.validate().is_ok());
        }
    }
}
