#[derive(Eq, PartialEq, Hash, PartialOrd, Ord, Clone)]
pub struct Height(pub u128);

impl Height {
    pub fn increment(&self) -> Self {
        Height(self.0 + 1)
    }
}

impl From<u128> for Height {
    fn from(v: u128) -> Self {
        Height(v)
    }
}
