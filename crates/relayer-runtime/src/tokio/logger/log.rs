use core::cell::RefCell;
use core::fmt::{self, Display};

use crate::tokio::logger::value::LogValue;

pub struct Log<'a> {
    pub fields: RefCell<Vec<(&'a str, LogValue<'a>)>>,
}

impl<'a> Log<'a> {
    pub fn new() -> Self {
        Self {
            fields: RefCell::new(Vec::new()),
        }
    }
}

impl<'a> Display for Log<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_map()
            .entries(self.fields.borrow().iter().map(|&(ref k, ref v)| (*k, v)))
            .finish()
    }
}
