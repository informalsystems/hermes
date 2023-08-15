use core::cell::RefCell;
use core::fmt::{self, Display};

use crate::types::log::value::LogValue;

#[derive(Default)]
pub struct Log<'a> {
    pub fields: RefCell<Vec<(&'a str, LogValue<'a>)>>,
}

impl<'a> Display for Log<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_map()
            .entries(self.fields.borrow().iter().map(|&(k, ref v)| (k, v)))
            .finish()
    }
}
