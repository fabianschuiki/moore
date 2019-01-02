// Copyright (c) 2017 Fabian Schuiki

use grind::Grinder;
use std::collections::VecDeque;

pub struct Lookahead<T: Grinder> {
    inner: T,
    buffer: VecDeque<T::Item>,
}

impl<T> Lookahead<T>
where
    T: Grinder,
{
    pub fn new(inner: T) -> Lookahead<T> {
        Lookahead {
            inner: inner,
            buffer: VecDeque::new(),
        }
    }

    pub fn lookahead(&mut self, offset: usize) -> &T::Item {
        for _ in self.buffer.len()..offset + 1 {
            self.buffer.push_back(self.inner.next());
        }
        &self.buffer[offset]
    }

    pub fn undo(&mut self, item: T::Item) {
        self.buffer.push_front(item);
    }
}

impl<T> Grinder for Lookahead<T>
where
    T: Grinder,
{
    type Item = T::Item;
    type Error = T::Error;

    fn emit(&mut self, err: Self::Error) {
        self.inner.emit(err)
    }

    fn next(&mut self) -> Self::Item {
        match self.buffer.pop_front() {
            Some(v) => v,
            None => self.inner.next(),
        }
    }
}

impl<T> From<T> for Lookahead<T>
where
    T: Grinder,
{
    fn from(inner: T) -> Lookahead<T> {
        Lookahead::new(inner)
    }
}
