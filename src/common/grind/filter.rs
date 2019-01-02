// Copyright (c) 2017 Fabian Schuiki

use crate::grind::{Chisel, Grinder};

pub struct Filter<T: Grinder, F> {
    inner: T,
    func: F,
}

impl<T, F> Filter<T, F>
where
    T: Grinder,
{
    pub fn new(inner: T, func: F) -> Filter<T, F> {
        Filter {
            inner: inner,
            func: func,
        }
    }
}

impl<T, F> Grinder for Filter<T, F>
where
    T: Grinder,
    F: Fn(&<T::Item as Chisel>::Value) -> bool,
{
    type Item = T::Item;
    type Error = T::Error;

    fn emit(&mut self, err: Self::Error) {
        self.inner.emit(err)
    }

    fn next(&mut self) -> Self::Item {
        loop {
            let n = self.inner.next();
            if match n.value_ref() {
                Some(v) => (self.func)(v),
                None => true,
            } {
                return n;
            }
        }
    }
}
