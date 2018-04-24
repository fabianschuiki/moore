// Copyright (c) 2018 Fabian Schuiki

//! Multi-type arena allocation

#![deny(missing_docs)]

use std::borrow::Cow;

/// Allocates values.
pub trait Alloc<'a, 't, T> {
    /// Allocate a value of type `T`.
    fn alloc(&'a self, value: T) -> &'t mut T;
}

impl<'z, 'a, 'p: 'a, 't, T> Alloc<'z, 't, T> for &'p Alloc<'a, 't, T> {
    fn alloc(&'z self, value: T) -> &'t mut T {
        Alloc::alloc(*self, value)
    }
}

/// Allocates values into itself.
///
/// This is merely a marker trait that you should not implement yourself. It is
/// implemented automatically on anything that supports `Alloc<'a, 'a, T>` for
/// any `'a`. The allocated values have the same lifetime as `&self`.
pub trait AllocSelf<T>: for<'a> Alloc<'a, 'a, T> {}

// Implement `AllocSelf` for anything that supports the proper `Alloc`.
impl<T, A> AllocSelf<T> for A
where
    A: for<'a> Alloc<'a, 'a, T>,
{
}

/// Allocates values into some arena.
///
/// This is merely a marker trait that you should not implement yourself. It is
/// implemented automatically on anything that supports `Alloc<'a, 't, T>` for
/// any `'a`. The allocated values have the lifetime `'t`.
pub trait AllocInto<'t, T>: for<'a> Alloc<'a, 't, T> {}

// Implement `AllocInto` for anything that supports the proper `Alloc`.
impl<'t, T, A> AllocInto<'t, T> for A
where
    A: for<'a> Alloc<'a, 't, T>,
{
}

/// Allocates values implementing `ToOwned`.
///
/// This is merely a marker trait that you should not implement yourself. It is
/// implemented automatically on anything that supports `Alloc`.
pub trait AllocOwned<'a, 't, T: ToOwned + ?Sized> {
    /// Allocate a value of type `T: ToOwned` into this arena.
    ///
    /// This function differs from `Alloc::alloc` in that it takes `T::Owned`
    /// and returns `&T`.
    fn alloc_owned(&'a self, value: <T as ToOwned>::Owned) -> &'t mut T;

    /// Conditionally allocate a value of type `Cow<T>`.
    ///
    /// If the value is `Cow::Owned`, allocates and returns a reference to it;
    /// if it is `Cow::Borrowed`, returns the reference without allocation. This
    /// requires that the borrow in `Cow` has the same lifetime as the allocated
    /// reference will have, as indicated by the type `Cow<'t, T> -> &'t T`. Use
    /// `force_alloc` if you don't have such a lifetime guarantee.
    fn maybe_alloc(&'a self, value: Cow<'t, T>) -> &'t T {
        match value {
            Cow::Borrowed(x) => x,
            Cow::Owned(x) => self.alloc_owned(x),
        }
    }

    /// Forcefully allocate a value of type `Cow<T>`.
    ///
    /// Regardless of whether the value is `Cow::Owned` or `Cow::Borrowed`, it
    /// is converted to the owned value via `ToOwned::into_owned()` and
    /// allocated. This function is useful if you have no guarantee that the
    /// lifetime of the borrow in `Cow` has the same lifetime as the allocated
    /// reference, as indicated by the type `Cow<T> -> &'t T'. Use `maybe_alloc`
    /// if you do have such a lifetime guarantee.
    fn force_alloc(&'a self, value: Cow<T>) -> &'t T {
        self.alloc_owned(value.into_owned())
    }
}

// Implement `AllocOwned` for anything that supports the proper `Alloc` and for
// any types that implement `ToOwned` with `Owned` equal to the type.
impl<'a, 't, T: ToOwned<Owned = T>> AllocOwned<'a, 't, T> for Alloc<'a, 't, T> {
    fn alloc_owned(&'a self, value: T) -> &'t mut T {
        self.alloc(value)
    }
}

/// Allocates values implementing `ToOwned` into itself.
///
/// This is merely a marker trait that you should not implement yourself. It is
/// implemented automatically on anything that supports `AllocOwned<'a, 'a, T>`
/// for any `'a`. The allocated values have the same lifetime as `&self`.
pub trait AllocOwnedSelf<T: ToOwned + ?Sized>: for<'a> AllocOwned<'a, 'a, T> {}

// Implement `AllocOwnedSelf` for anything that supports the proper
// `AllocOwned`.
impl<T, A> AllocOwnedSelf<T> for A
where
    T: ToOwned + ?Sized,
    A: for<'a> AllocOwned<'a, 'a, T>,
{
}

/// Allocates values implementing `ToOwned` into some arena.
///
/// This is merely a marker trait that you should not implement yourself. It is
/// implemented automatically on anything that supports `AllocOwned<'a, 't, T>`
/// for any `'a`. The allocated values have the lifetime `'t`.
pub trait AllocOwnedInto<'t, T: ToOwned + ?Sized>: for<'a> AllocOwned<'a, 't, T> {}

// Implement `AllocOwnedInto` for anything that supports the proper
// `AllocOwned`.
impl<'t, T, A> AllocOwnedInto<'t, T> for A
where
    T: ToOwned + ?Sized,
    A: for<'a> AllocOwned<'a, 't, T>,
{
}

/// Generate a collection of arenas for different types.
#[macro_export]
macro_rules! make_arenas {
    ($(#[$arena_attr:meta])* pub struct $arena_name:ident { $($name:ident: $type:ty,)* }) => {
        make_arenas!{ IMPL $($arena_attr),*; $arena_name; []; $($name: $type,)* }
    };

    ($(#[$arena_attr:meta])* pub struct $arena_name:ident<$($lt:tt),+> { $($name:ident: $type:ty,)* }) => {
        make_arenas!{ IMPL $($arena_attr),*; $arena_name; [$($lt),+]; $($name: $type,)* }
    };

    (IMPL $($arena_attr:meta),*; $arena_name:ident; [$($lt:tt),*]; $($name:ident: $type:ty,)*) => {
        $(#[$arena_attr])*
        #[allow(missing_docs)]
        pub struct $arena_name<$($lt),*> {
            $(pub $name: ::typed_arena::Arena<$type>,)*
        }

        make_arenas!(STRUCT_IMPL $arena_name; [$($lt),*]; $($name: $type,)*);
    };

    (STRUCT_IMPL $arena_name:ident; [$($lt:tt),*]; $($name:ident: $type:ty,)*) => {
        impl<$($lt),*> $arena_name<$($lt),*> {
            /// Create a new arena.
            pub fn new() -> $arena_name<$($lt),*> {
                $arena_name {
                    $($name: ::typed_arena::Arena::new(),)*
                }
            }
        }

        impl<$($lt),*> Default for $arena_name<$($lt),*> {
            fn default() -> $arena_name<$($lt),*> {
                $arena_name::new()
            }
        }

        make_arenas!(TRAIT_IMPL $arena_name; [$($lt),*]; $($name: $type,)*);
    };

    (TRAIT_IMPL $arena_name:ident; [$($lt:tt),*]; $name:ident: $type:ty, $($tail_name:ident: $tail_type:ty,)*) => {
        impl<'a, $($lt),*> $crate::arenas::Alloc<'a, 'a, $type> for $arena_name<$($lt),*> where $($lt: 'a),* {
            fn alloc(&'a self, value: $type) -> &'a mut $type {
                self.$name.alloc(value)
            }
        }

        make_arenas!(TRAIT_IMPL $arena_name; [$($lt),*]; $($tail_name: $tail_type,)*);
    };

    (TRAIT_IMPL $arena_name:ident; [$($lt:tt),*];) => {}
}
