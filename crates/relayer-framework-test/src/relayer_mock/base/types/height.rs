use std::fmt::Display;

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Height(pub u128);

impl Height {
    pub fn increment(&self) -> Self {
        Height(self.0 + 1)
    }
}

impl Display for Height {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Height({})", self.0)?;
        Ok(())
    }
}

impl From<u128> for Height {
    fn from(v: u128) -> Self {
        Height(v)
    }
}
