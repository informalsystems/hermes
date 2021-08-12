pub mod data;

use core::cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd};
use core::fmt::{self, Debug, Display};
use core::iter::{IntoIterator, Iterator};
use core::marker::PhantomData;

pub struct Tagged<Tag, Value>(pub Value, pub PhantomData<Tag>);

pub struct DualTagged<Tag1, Tag2, Value>(pub Value, pub PhantomData<(Tag1, Tag2)>);

pub enum EitherTagged<Tag1, Tag2, Value> {
    Left(Tagged<Tag1, Value>),
    Right(Tagged<Tag2, Value>),
}

impl<Tag, Value> Tagged<Tag, Value> {
    pub fn new(value: Value) -> Self {
        Tagged(value, PhantomData)
    }

    pub fn new_with_tag(tag: PhantomData<Tag>, value: Value) -> Self {
        Tagged(value, tag)
    }

    pub fn value(&self) -> &Value {
        &self.0
    }

    pub fn mut_value(&mut self) -> &mut Value {
        &mut self.0
    }

    pub fn tag<V>(&self, value: V) -> Tagged<Tag, V> {
        Tagged::new(value)
    }

    pub fn untag(self) -> Value {
        self.0
    }

    pub fn add_tag<Tag2>(self) -> DualTagged<Tag, Tag2, Value> {
        DualTagged::new(self.untag())
    }

    pub fn map<T>(&self, mapper: impl FnOnce(&Value) -> T) -> Tagged<Tag, T> {
        Tagged::new(mapper(self.value()))
    }

    pub fn map_into<T>(self, mapper: impl FnOnce(Value) -> T) -> Tagged<Tag, T> {
        Tagged::new(mapper(self.0))
    }
}

impl<Tag1, Tag2, Value> DualTagged<Tag1, Tag2, Value> {
    pub fn new(value: Value) -> Self {
        DualTagged(value, PhantomData)
    }

    pub fn value(&self) -> &Value {
        &self.0
    }

    pub fn untag(self) -> Value {
        self.0
    }

    pub fn dual_map<T>(&self, mapper: impl FnOnce(&Value) -> T) -> DualTagged<Tag1, Tag2, T> {
        DualTagged::new(mapper(self.value()))
    }

    pub fn map<T>(&self, mapper: impl FnOnce(&Value) -> T) -> Tagged<Tag1, T> {
        Tagged::new(mapper(self.value()))
    }

    pub fn map_flipped<T>(&self, mapper: impl FnOnce(&Value) -> T) -> Tagged<Tag2, T> {
        Tagged::new(mapper(self.value()))
    }

    pub fn map_into<T>(self, mapper: impl FnOnce(Value) -> T) -> Tagged<Tag1, T> {
        Tagged::new(mapper(self.0))
    }

    pub fn dual_map_into<T>(self, mapper: impl FnOnce(Value) -> T) -> DualTagged<Tag1, Tag2, T> {
        DualTagged::new(mapper(self.0))
    }
}

// impl <Tag, Value> Iterator for TaggedVec<Tag, Value> {
//     type Item = Tagged<Tag, Value>;

// }

impl<Tag, Value> Tagged<Tag, Option<Value>> {
    pub fn transpose(self) -> Option<Tagged<Tag, Value>> {
        self.0.map(Tagged::new)
    }
}

impl<Tag, Value, E> Tagged<Tag, Result<Value, E>> {
    pub fn transpose(self) -> Result<Tagged<Tag, Value>, E> {
        self.0.map(Tagged::new)
    }
}

impl<Tag, Value> Tagged<Tag, Vec<Value>> {
    pub fn transpose(self) -> Vec<Tagged<Tag, Value>> {
        self.into_iter().collect()
    }
}

impl<Tag, Value: Clone> Clone for Tagged<Tag, Value> {
    fn clone(&self) -> Self {
        Self::new(self.0.clone())
    }
}

impl<Tag, Value: Default> Default for Tagged<Tag, Value> {
    fn default() -> Self {
        Self::new(Value::default())
    }
}

impl<Tag, Value: Debug> Debug for Tagged<Tag, Value> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(self.value(), f)
    }
}

impl<Tag, Value: Display> Display for Tagged<Tag, Value> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self.value(), f)
    }
}

impl<Tag, Value: PartialEq> PartialEq for Tagged<Tag, Value> {
    fn eq(&self, other: &Self) -> bool {
        self.value().eq(other.value())
    }
}

impl<Tag, Value: Eq> Eq for Tagged<Tag, Value> {}

impl<Tag, Value: PartialOrd> PartialOrd for Tagged<Tag, Value> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.value().partial_cmp(other.value())
    }
}

impl<Tag, Value: Ord> Ord for Tagged<Tag, Value> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.value().cmp(other.value())
    }
}

impl<Tag1, Tag2, Value> DualTagged<Tag1, Tag2, Option<Value>> {
    pub fn transpose(self) -> Option<DualTagged<Tag1, Tag2, Value>> {
        self.0.map(DualTagged::new)
    }
}

impl<Tag1, Tag2, Value, E> DualTagged<Tag1, Tag2, Result<Value, E>> {
    pub fn transpose(self) -> Result<DualTagged<Tag1, Tag2, Value>, E> {
        self.0.map(DualTagged::new)
    }
}

impl<Tag1, Tag2, Value: Clone> Clone for DualTagged<Tag1, Tag2, Value> {
    fn clone(&self) -> Self {
        Self::new(self.0.clone())
    }
}

impl<Tag1, Tag2, Value: Debug> Debug for DualTagged<Tag1, Tag2, Value> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(self.value(), f)
    }
}

impl<Tag1, Tag2, Value: Display> Display for DualTagged<Tag1, Tag2, Value> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self.value(), f)
    }
}

impl<Tag1, Tag2, Value: PartialEq> PartialEq for DualTagged<Tag1, Tag2, Value> {
    fn eq(&self, other: &Self) -> bool {
        self.value().eq(other.value())
    }
}

impl<Tag1, Tag2, Value: Eq> Eq for DualTagged<Tag1, Tag2, Value> {}

impl<Tag1, Tag2, Value: PartialOrd> PartialOrd for DualTagged<Tag1, Tag2, Value> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.value().partial_cmp(other.value())
    }
}

impl<Tag1, Tag2, Value: Ord> Ord for DualTagged<Tag1, Tag2, Value> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.value().cmp(other.value())
    }
}

pub struct TaggedIterator<Tag, It>(Tagged<Tag, It>);

impl<Tag, It: Iterator> Iterator for TaggedIterator<Tag, It> {
    type Item = Tagged<Tag, It::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0 .0.next().map(Tagged::new)
    }
}

impl<Tag, Value: IntoIterator> IntoIterator for Tagged<Tag, Value> {
    type Item = Tagged<Tag, Value::Item>;

    type IntoIter = TaggedIterator<Tag, Value::IntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        TaggedIterator(self.map_into(|v| v.into_iter()))
    }
}
