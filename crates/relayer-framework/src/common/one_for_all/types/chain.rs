#[derive(Clone)]
pub struct OfaChainWrapper<Chain> {
    pub chain: Chain,
}

impl<Chain> OfaChainWrapper<Chain> {
    pub fn new(chain: Chain) -> Self {
        Self { chain }
    }
}
