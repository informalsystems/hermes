use core::fmt::{self, Debug, Display};

pub enum LogValue<'a> {
    Display(&'a dyn Display),
    Debug(&'a dyn Debug),
}

impl<'a> Debug for LogValue<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Display(value) => Display::fmt(*value, f),
            Self::Debug(value) => Debug::fmt(*value, f),
        }
    }
}
