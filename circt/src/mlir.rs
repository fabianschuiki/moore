use circt_sys::*;

pub struct Context(MlirContext);

impl Context {
    pub fn new() -> Self {
        Self(unsafe { mlirContextCreate() })
    }

    pub fn raw(&self) -> MlirContext {
        self.0
    }

    pub fn load_dialect(&self, dialect: DialectHandle) {
        unsafe { mlirDialectHandleLoadDialect(dialect.0, self.0) };
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe { mlirContextDestroy(self.0) }
    }
}

#[derive(Copy, Clone)]
pub struct DialectHandle(MlirDialectHandle);

impl DialectHandle {
    pub fn from_raw(raw: MlirDialectHandle) -> Self {
        Self(raw)
    }
}

/// A trait implemented by anything that wraps an MLIR operation.
pub trait OperationExt {
    fn raw_operation(&self) -> MlirOperation;

    fn operation(&self) -> Operation {
        Operation(self.raw_operation())
    }
}

pub struct Operation(MlirOperation);

impl OperationExt for Operation {
    fn raw_operation(&self) -> MlirOperation {
        self.0
    }
}

pub struct ModuleOp(MlirOperation);

impl OperationExt for ModuleOp {
    fn raw_operation(&self) -> MlirOperation {
        self.0
    }
}
