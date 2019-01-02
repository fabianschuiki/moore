// Copyright (c) 2017 Fabian Schuiki

use grind::Grinder;
use std;

pub struct Peekable<T: Grinder> {
    inner: T,
    peek: T::Item,
}

impl<T> Peekable<T>
where
    T: Grinder,
{
    pub fn new(mut inner: T) -> Peekable<T> {
        let peek = inner.next();
        Peekable {
            inner: inner,
            peek: peek,
        }
    }

    pub fn peek(&self) -> &T::Item {
        &self.peek
    }
}

impl<T> Grinder for Peekable<T>
where
    T: Grinder,
{
    type Item = T::Item;
    type Error = T::Error;

    fn emit(&mut self, err: Self::Error) {
        self.inner.emit(err)
    }

    fn next(&mut self) -> Self::Item {
        let mut n = self.inner.next();
        std::mem::swap(&mut self.peek, &mut n);
        n
    }
}

impl<T> From<T> for Peekable<T>
where
    T: Grinder,
{
    fn from(inner: T) -> Peekable<T> {
        Peekable::new(inner)
    }
}
