// Copyright (c) 2016-2021 Fabian Schuiki

//! Utilities to deal with the MLIR context.

use crate::crate_prelude::*;
use crate::mlir::DialectHandle;

/// An MLIR context.
#[derive(Copy, Clone)]
pub struct Context(MlirContext);

/// An owned MLIR context.
pub type OwnedContext = Owned<Context>;

impl Context {
    /// Load a dialect into this context.
    pub fn load_dialect(&self, dialect: DialectHandle) {
        unsafe {
            mlirDialectHandleLoadDialect(dialect.0, self.0);
            mlirDialectHandleRegisterDialect(dialect.0, self.0);
        }
    }

    /// Get an interned identifier.
    pub fn get_identifier(&self, ident: &str) -> MlirIdentifier {
        unsafe { mlirIdentifierGet(self.raw(), mlirStringRefCreateFromStr(ident)) }
    }

    /// Change whether this MLIR context allows unregistered dialect ops.
    pub fn set_allow_unregistered_dialects(&self, allow: bool) {
        unsafe { mlirContextSetAllowUnregisteredDialects(self.raw(), allow) }
    }

    /// Change whether this MLIR context allows unregistered dialect ops.
    pub fn are_unregistered_dialects_allowed(&self) -> bool {
        unsafe { mlirContextGetAllowUnregisteredDialects(self.raw()) }
    }
}

impl WrapRaw for Context {
    type RawType = MlirContext;
    fn from_raw(raw: MlirContext) -> Self {
        Self(raw)
    }
    fn raw(&self) -> MlirContext {
        self.0
    }
}

impl Owned<Context> {
    /// Create a new MLIR context.
    pub fn new() -> Self {
        Self(Context::from_raw(unsafe { mlirContextCreate() }))
    }
}

impl IntoOwned for Context {
    fn destroy(&mut self) {
        unsafe { mlirContextDestroy(self.0) }
    }
}
