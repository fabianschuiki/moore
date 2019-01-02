// Copyright (c) 2016-2019 Fabian Schuiki

//! An implementation of the verilog type system.

/// A verilog type.
pub type Type<'t> = &'t TypeKind<'t>;

/// Type data.
#[derive(Debug)]
pub enum TypeKind<'t> {
    Void,
    Bit,
    Logic,
    Reg,
    Dummy(std::marker::PhantomData<&'t ()>),
}

impl<'t> TypeKind<'t> {
    /// Check if this is the void type.
    pub fn is_void(&self) -> bool {
        match *self {
            TypeKind::Void => true,
            _ => false,
        }
    }
}
