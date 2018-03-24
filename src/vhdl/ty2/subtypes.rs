// Copyright (c) 2017-2018 Fabian Schuiki

//! The subtyping mechanism.

use std::fmt::{self, Debug, Display};

/// An interface for dealing with subtypes.
pub trait Subtype: Debug + Display {
}
