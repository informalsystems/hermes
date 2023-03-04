use core::fmt::{self, Debug, Display};

pub enum LogValue<'a> {
    Display(&'a dyn Display),
    Debug(&'a dyn Debug),
    List(&'a [LogValue<'a>]),
    Nested(Vec<(&'a str, LogValue<'a>)>),
}

impl<'a> Debug for LogValue<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Display(value) => Display::fmt(*value, f),
            Self::Debug(value) => Debug::fmt(*value, f),
            Self::List(values) => f.debug_list().entries(values.iter()).finish(),
            Self::Nested(values) => f
                .debug_map()
                .entries(values.iter().map(|&(k, ref v)| (k, v)))
                .finish(),
        }
    }
}
