use crate::traits::solomachine::SolomachineChain;

pub struct SolomachineChainWrapper<Chain> {
    pub chain: Chain,
}

impl<Chain: SolomachineChain> SolomachineChainWrapper<Chain> {
    pub fn new(chain: Chain) -> Self {
        SolomachineChainWrapper { chain }
    }
}
