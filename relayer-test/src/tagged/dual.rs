use core::cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd};
use core::fmt::{self, Debug, Display};
use core::iter::{IntoIterator, Iterator};
use core::marker::PhantomData;

pub struct Tagged<TagA, TagB, Value>(pub Value, PhantomData<(TagA, TagB)>);

impl<TagA, TagB, Value> Tagged<TagA, TagB, Value> {
    pub fn new(value: Value) -> Self {
        Tagged(value, PhantomData)
    }

    pub fn value(&self) -> &Value {
        &self.0
    }

    pub fn into_value(self) -> Value {
        self.0
    }

    pub fn as_ref<'a>(&'a self) -> Tagged<TagA, TagB, &'a Value> {
        Tagged::new(&self.0)
    }

    pub fn flip(self) -> Tagged<TagB, TagA, Value> {
        Tagged::new(self.0)
    }

    pub fn transmute<TagC, TagD>(self) -> Tagged<TagC, TagD, Value> {
        Tagged::new(self.0)
    }

    pub fn map<T>(&self, mapper: impl FnOnce(&Value) -> T) -> Tagged<TagA, TagB, T> {
        Tagged::new(mapper(&self.0))
    }

    pub fn map_into<T>(self, mapper: impl FnOnce(Value) -> T) -> Tagged<TagA, TagB, T> {
        Tagged::new(mapper(self.0))
    }

    pub fn contra_map<T>(&self, mapper: impl FnOnce(&Value) -> T) -> Tagged<TagB, TagA, T> {
        Tagged::new(mapper(&self.0))
    }

    pub fn contra_map_into<T>(self, mapper: impl FnOnce(Value) -> T) -> Tagged<TagB, TagA, T> {
        Tagged::new(mapper(self.0))
    }
}

impl<Tag1, Tag2, Value> Tagged<Tag1, Tag2, Option<Value>> {
    pub fn transpose(self) -> Option<Tagged<Tag1, Tag2, Value>> {
        self.0.map(Tagged::new)
    }
}

impl<Tag1, Tag2, Value, E> Tagged<Tag1, Tag2, Result<Value, E>> {
    pub fn transpose(self) -> Result<Tagged<Tag1, Tag2, Value>, E> {
        self.0.map(Tagged::new)
    }
}

impl<Tag1, Tag2, Value: Clone> Clone for Tagged<Tag1, Tag2, Value> {
    fn clone(&self) -> Self {
        Self::new(self.0.clone())
    }
}

impl<Tag1, Tag2, Value: Debug> Debug for Tagged<Tag1, Tag2, Value> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(self.value(), f)
    }
}

impl<Tag1, Tag2, Value: Display> Display for Tagged<Tag1, Tag2, Value> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self.value(), f)
    }
}

impl<Tag1, Tag2, Value: PartialEq> PartialEq for Tagged<Tag1, Tag2, Value> {
    fn eq(&self, other: &Self) -> bool {
        self.value().eq(other.value())
    }
}

impl<Tag1, Tag2, Value: Eq> Eq for Tagged<Tag1, Tag2, Value> {}

impl<Tag1, Tag2, Value: PartialOrd> PartialOrd for Tagged<Tag1, Tag2, Value> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.value().partial_cmp(other.value())
    }
}

impl<Tag1, Tag2, Value: Ord> Ord for Tagged<Tag1, Tag2, Value> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.value().cmp(other.value())
    }
}

pub struct TaggedIterator<TagA, TagB, It>(Tagged<TagA, TagB, It>);

impl<TagA, TagB, It: Iterator> Iterator for TaggedIterator<TagA, TagB, It> {
    type Item = Tagged<TagA, TagB, It::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0 .0.next().map(Tagged::new)
    }
}

impl<TagA, TagB, Value: IntoIterator> IntoIterator for Tagged<TagA, TagB, Value> {
    type Item = Tagged<TagA, TagB, Value::Item>;

    type IntoIter = TaggedIterator<TagA, TagB, Value::IntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        TaggedIterator(self.map_into(|v| v.into_iter()))
    }
}
