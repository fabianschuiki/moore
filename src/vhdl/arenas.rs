// Copyright (c) 2018 Fabian Schuiki

//! Multi-type arena allocation

#![deny(missing_docs)]

/// Allocates objects into an arena.
pub trait Alloc<T> {
    /// Allocate an object of type `T` into this arena.
    fn alloc(&self, value: T) -> &mut T;
}

/// Allocates objects into a remote arena.
///
/// In contrast to `Alloc`, the lifetime of the references returned by this
/// trait are not bound to the trait itself. Rather, the lifetime is a parameter
/// of the trait itself. This allows context objects to be created that hold a
/// reference to an arena, and allow for direct allocation into that arena.
pub trait AllocInto<'t, T> {
    /// Allocate an object of type `T`.
    fn alloc(&self, value: T) -> &'t mut T;
}

impl<'t, T> AllocInto<'t, T> for &'t Alloc<T> {
    fn alloc(&self, value: T) -> &'t mut T {
        Alloc::alloc(*self, value)
    }
}

#[macro_export]
macro_rules! make_arenas {
    ($(#[$arena_attr:meta])* pub struct $arena_name:ident { $($name:ident: $type:ty,)* }) => (
        $(#[$arena_attr])*
        pub struct $arena_name {
            $(pub $name: Arena<$type>,)*
        }

        impl Default for $arena_name {
            fn default() -> $arena_name {
                $arena_name {
                    $($name: Arena::new(),)*
                }
            }
        }

        $(
            impl $crate::arenas::Alloc<$type> for $arena_name {
                fn alloc(&self, value: $type) -> &mut $type {
                    self.$name.alloc(value)
                }
            }
        )*
    );
}
