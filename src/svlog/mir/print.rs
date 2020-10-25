// Copyright (c) 2016-2020 Fabian Schuiki

//! A printer for the MIR.

use itertools::Itertools;
use std::collections::HashMap;
use std::fmt::Write;

#[derive(Default)]
pub struct Context {
    printed: HashMap<*const u8, PrintKey>,
}

impl Context {
    pub fn print(&mut self, outer: &mut impl Write, node: &impl Print) -> PrintKey {
        let key = node.id();
        if let Some(&num) = self.printed.get(&key) {
            num
        } else {
            let mut line = String::new();
            node.print_context(outer, &mut line, self).unwrap();
            let num = PrintKey(self.printed.len());
            self.printed.insert(key, num);
            write!(outer, "{} = {}\n", num, line).unwrap();
            num
        }
    }

    pub fn print_comma_separated<'a>(
        &mut self,
        outer: &mut impl Write,
        nodes: impl IntoIterator<Item = &'a (impl Print + 'a)>,
    ) -> String {
        nodes.into_iter().map(|x| self.print(outer, x)).join(", ")
    }
}

#[derive(Clone, Copy)]
pub struct PrintKey(usize);

impl std::fmt::Display for PrintKey {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "_{}", self.0)
    }
}

/// Support for MIR pretty printing.
pub trait Print {
    fn id(&self) -> *const u8 {
        self as *const _ as *const u8
    }

    fn print(&self, f: &mut impl Write) -> std::fmt::Result {
        let mut line = String::new();
        self.print_context(f, &mut line, &mut Context::default())?;
        write!(f, "{}", line)
    }

    fn print_context(
        &self,
        outer: &mut impl Write,
        inner: &mut impl Write,
        ctx: &mut Context,
    ) -> std::fmt::Result;
}

/// Implement `Print` for all references to something that can `Print`.
impl<'a, T: Print> Print for &'a T {
    fn id(&self) -> *const u8 {
        (**self).id()
    }

    fn print_context(
        &self,
        outer: &mut impl Write,
        inner: &mut impl Write,
        ctx: &mut Context,
    ) -> std::fmt::Result {
        (**self).print_context(outer, inner, ctx)
    }
}
