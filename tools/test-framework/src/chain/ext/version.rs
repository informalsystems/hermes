use crate::{
    chain::{
        cli::version::major_version,
        driver::ChainDriver,
    },
    error::Error,
    types::tagged::*,
};

pub trait ChainVersionMethodsExt {
    fn major_version(&self) -> Result<u64, Error>;
}

impl<'a, Chain: Send> ChainVersionMethodsExt for MonoTagged<Chain, &'a ChainDriver> {
    fn major_version(&self) -> Result<u64, Error> {
        major_version(&self.value().command_path)
    }
}
