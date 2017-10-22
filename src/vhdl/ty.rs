// Copyright (c) 2017 Fabian Schuiki

//! This module implements VHDL types.

use std;

#[derive(Debug, Clone)]
pub struct Ty<'a> {
	marker: std::marker::PhantomData<&'a ()>
}
