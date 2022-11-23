use alloc::collections::VecDeque;
use std::sync::{Arc, RwLock};

use crate::util::lock::LockExt;

/// A lightweight wrapper type around `Arc<RwLock<VecDeque<T>>>` so that
/// we can safely mutate it with regular reference instead of
/// mutable reference. We only expose subset of `VecDeque` methods
/// that does not return any inner reference, so that the `RefCell`
/// can never panic caused by simultaneous `borrow` and `borrow_mut`.
pub struct Queue<T>(Arc<RwLock<VecDeque<T>>>);

impl<T> Queue<T> {
    pub fn new() -> Self {
        Queue(Arc::new(RwLock::new(VecDeque::new())))
    }

    pub fn pop_front(&self) -> Option<T> {
        self.0.acquire_write().pop_front()
    }

    pub fn pop_back(&self) -> Option<T> {
        self.0.acquire_write().pop_back()
    }

    pub fn push_back(&self, val: T) {
        self.0.acquire_write().push_back(val)
    }

    pub fn push_front(&self, val: T) {
        self.0.acquire_write().push_front(val)
    }

    pub fn len(&self) -> usize {
        self.0.acquire_read().len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.acquire_read().is_empty()
    }

    pub fn into_vec(self) -> VecDeque<T> {
        self.0.acquire_write().drain(..).collect()
    }

    pub fn replace(&self, queue: VecDeque<T>) {
        *self.0.acquire_write() = queue;
    }

    pub fn take(&self) -> VecDeque<T> {
        self.0.acquire_write().drain(..).collect()
    }
}

impl<T: Clone> Queue<T> {
    pub fn clone_vec(&self) -> VecDeque<T> {
        self.0.acquire_read().clone()
    }
}

impl<T> Default for Queue<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> From<VecDeque<T>> for Queue<T> {
    fn from(deque: VecDeque<T>) -> Self {
        Queue(Arc::new(RwLock::new(deque)))
    }
}
