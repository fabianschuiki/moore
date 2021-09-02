use circt_sys::*;

pub struct Owned<T: IntoOwned>(T);

pub trait IntoOwned {
    fn destroy(&mut self);
}

impl<T: IntoOwned> Drop for Owned<T> {
    fn drop(&mut self) {
        self.0.destroy()
    }
}

impl<T: IntoOwned> std::ops::Deref for Owned<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

#[derive(Copy, Clone)]
pub struct Context(MlirContext);
pub type OwnedContext = Owned<Context>;

impl Context {
    pub fn from_raw(raw: MlirContext) -> Self {
        Self(raw)
    }

    pub fn raw(&self) -> MlirContext {
        self.0
    }

    pub fn load_dialect(&self, dialect: DialectHandle) {
        unsafe {
            mlirDialectHandleLoadDialect(dialect.0, self.0);
            mlirDialectHandleRegisterDialect(dialect.0, self.0);
        }
    }
}

impl Owned<Context> {
    pub fn new() -> Self {
        Self(Context::from_raw(unsafe { mlirContextCreate() }))
    }
}

impl IntoOwned for Context {
    fn destroy(&mut self) {
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

    fn dump(&self) {
        unsafe { mlirOperationDump(self.raw_operation()) };
    }

    fn context(&self) -> Context {
        unsafe { Context::from_raw(mlirOperationGetContext(self.raw_operation())) }
    }
}

pub struct Operation(MlirOperation);

impl OperationExt for Operation {
    fn raw_operation(&self) -> MlirOperation {
        self.0
    }
}

pub struct OperationState(MlirOperationState);

impl OperationState {
    pub fn new(op_name: &str, loc: MlirLocation) -> Self {
        Self(unsafe { mlirOperationStateGet(mlirStringRefCreateFromStr(op_name), loc) })
    }

    pub fn with_unknown_location(cx: Context, op_name: &str) -> Self {
        Self::new(op_name, unsafe { mlirLocationUnknownGet(cx.raw()) })
    }

    pub fn raw(&self) -> MlirOperationState {
        self.0
    }

    pub fn raw_mut(&mut self) -> &mut MlirOperationState {
        &mut self.0
    }

    pub fn build(mut self) -> Operation {
        unsafe { Operation(mlirOperationCreate(self.raw_mut())) }
    }
}
