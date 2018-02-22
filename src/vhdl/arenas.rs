// Copyright (c) 2018 Fabian Schuiki

//! Multi-type arena allocation

#![deny(missing_docs)]

/// Allocates objects into an arena.
pub trait Alloc<T> {
    /// Allocate an object of type `T` into this arena.
    fn alloc(&self, value: T) -> &mut T;
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
            impl Alloc<$type> for $arena_name {
                fn alloc(&self, value: $type) -> &mut $type {
                    self.$name.alloc(value)
                }
            }
        )*
    );
}
