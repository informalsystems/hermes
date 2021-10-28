pub trait Tag {}

impl<T> Tag for T {}

pub fn new_tag() -> impl Tag {}
