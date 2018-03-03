// Copyright (c) 2018 Fabian Schuiki

//! Builtin libraries, packages, types, and functions.

use std::collections::HashSet;

use common::score::NodeRef;
use common::source::*;
use common::name::*;

use score::{ResolvableName, ScoreBoard, ScopeRef, LibRef, BuiltinPkgRef, Def, TypeDeclRef, EnumRef};
use scope::Scope;
use ty::*;

// Define some global references for the builtins.
lazy_static! {
	/// A reference to the root scope where all builtins are declared.
	pub static ref ROOT_SCOPE_REF: ScopeRef = LibRef::alloc().into();
	/// A reference to the library `STD`.
	pub static ref STD_LIB_REF: LibRef = LibRef::alloc();
	/// A reference to the package `STANDARD`.
	pub static ref STANDARD_PKG_REF: BuiltinPkgRef = BuiltinPkgRef::alloc();
	/// A reference to the package `TEXTIO`.
	pub static ref TEXTIO_PKG_REF: BuiltinPkgRef = BuiltinPkgRef::alloc();
	/// A reference to the package `ENV`.
	pub static ref ENV_PKG_REF: BuiltinPkgRef = BuiltinPkgRef::alloc();

	// A reference to the type `BOOLEAN`.
	pub static ref BOOLEAN_TYPE_REF: TypeDeclRef = TypeDeclRef::alloc();
	// A reference to the type `BIT`.
	pub static ref BIT_TYPE_REF: TypeDeclRef = TypeDeclRef::alloc();
	// A reference to the type `SEVERITY_LEVEL`.
	pub static ref SEVERITY_LEVEL_TYPE_REF: TypeDeclRef = TypeDeclRef::alloc();
	// A reference to the type `INTEGER`.
	pub static ref INTEGER_TYPE_REF: TypeDeclRef = TypeDeclRef::alloc();
	// A reference to the type `NATURAL`.
	pub static ref NATURAL_TYPE_REF: TypeDeclRef = TypeDeclRef::alloc();
	// A reference to the type `POSITIVE`.
	pub static ref POSITIVE_TYPE_REF: TypeDeclRef = TypeDeclRef::alloc();
	// A reference to the type `FILE_OPEN_KIND`.
	pub static ref FILE_OPEN_KIND_TYPE_REF: TypeDeclRef = TypeDeclRef::alloc();
	// A reference to the type `FILE_OPEN_STATUS`.
	pub static ref FILE_OPEN_STATUS_TYPE_REF: TypeDeclRef = TypeDeclRef::alloc();
}

/// Add the definition for a builtin resolvable name to a scope.
fn define_builtin(scope: &mut Scope, name: ResolvableName, def: Def) {
	scope.defs.insert(name, vec![Spanned::new(def, INVALID_SPAN)]);
}

/// Add the definition for a builtin identifier to a scope.
fn define_builtin_ident(scope: &mut Scope, name: &str, def: Def) {
	let name = get_name_table().intern(name, false);
	define_builtin(scope, name.into(), def)
}

/// Add the definition for a builtin bit literal to a scope.
fn define_builtin_bit(scope: &mut Scope, bit: char, def: Def) {
	define_builtin(scope, bit.into(), def)
}

// Define the scopes of the builtins.
lazy_static! {
	/// The root scope.
	///
	/// It contains definitions equal to `library std; use std.standard.all;`
	pub static ref ROOT_SCOPE: Scope = {
		let mut scope = Scope::new(None);
		define_builtin_ident(&mut scope, "std", Def::Lib(*STD_LIB_REF));
		scope.imported_scopes.insert((*STANDARD_PKG_REF).into());
		scope
	};

	/// The scope of the library `STD`.
	pub static ref STD_LIB_SCOPE: Scope = {
		let mut scope = Scope::new(Some(*ROOT_SCOPE_REF));
		define_builtin_ident(&mut scope, "standard", Def::BuiltinPkg(*STANDARD_PKG_REF));
		define_builtin_ident(&mut scope, "textio", Def::BuiltinPkg(*TEXTIO_PKG_REF));
		define_builtin_ident(&mut scope, "env", Def::BuiltinPkg(*ENV_PKG_REF));
		scope
	};

	/// The scope of the package `STANDARD`.
	pub static ref STANDARD_PKG_SCOPE: Scope = {
		let mut scope = Scope::new(Some((*STD_LIB_REF).into()));

		// `type BOOLEAN is (FALSE, TRUE)`
		define_builtin_ident(&mut scope, "boolean", Def::Type(*BOOLEAN_TYPE_REF));
		define_builtin_ident(&mut scope, "false", Def::Enum(EnumRef(*BOOLEAN_TYPE_REF, 0)));
		define_builtin_ident(&mut scope, "true", Def::Enum(EnumRef(*BOOLEAN_TYPE_REF, 1)));

		// `type BIT is ('0', '1')`
		define_builtin_ident(&mut scope, "bit", Def::Type(*BIT_TYPE_REF));
		define_builtin_bit(&mut scope, '0', Def::Enum(EnumRef(*BIT_TYPE_REF, 0)));
		define_builtin_bit(&mut scope, '1', Def::Enum(EnumRef(*BIT_TYPE_REF, 1)));

		// `type SEVERITY_LEVEL is (NOTE, WARNING, ERROR, FAILURE)`
		define_builtin_ident(&mut scope, "severity_level", Def::Type(*SEVERITY_LEVEL_TYPE_REF));
		define_builtin_ident(&mut scope, "note", Def::Enum(EnumRef(*SEVERITY_LEVEL_TYPE_REF, 0)));
		define_builtin_ident(&mut scope, "warning", Def::Enum(EnumRef(*SEVERITY_LEVEL_TYPE_REF, 1)));
		define_builtin_ident(&mut scope, "error", Def::Enum(EnumRef(*SEVERITY_LEVEL_TYPE_REF, 2)));
		define_builtin_ident(&mut scope, "failure", Def::Enum(EnumRef(*SEVERITY_LEVEL_TYPE_REF, 3)));

		// `type INTEGER is range ... to ...`
		define_builtin_ident(&mut scope, "integer", Def::Type(*INTEGER_TYPE_REF));

		// `subtype NATURAL is range 0 to ...`
		define_builtin_ident(&mut scope, "natural", Def::Type(*NATURAL_TYPE_REF));

		// `subtype POSITIVE is range 1 to ...`
		define_builtin_ident(&mut scope, "positive", Def::Type(*POSITIVE_TYPE_REF));

		// `type FILE_OPEN_KIND is (READ_MODE, WRITE_MODE, APPEND_MODE)`
		define_builtin_ident(&mut scope, "file_open_kind", Def::Type(*FILE_OPEN_KIND_TYPE_REF));
		define_builtin_ident(&mut scope, "read_mode", Def::Enum(EnumRef(*FILE_OPEN_KIND_TYPE_REF, 0)));
		define_builtin_ident(&mut scope, "write_mode", Def::Enum(EnumRef(*FILE_OPEN_KIND_TYPE_REF, 1)));
		define_builtin_ident(&mut scope, "append_mode", Def::Enum(EnumRef(*FILE_OPEN_KIND_TYPE_REF, 2)));

		// `type FILE_OPEN_STATUS is (OPEN_OK, STATUS_ERROR, NAME_ERROR, MODE_ERROR)`
		define_builtin_ident(&mut scope, "file_open_status", Def::Type(*FILE_OPEN_STATUS_TYPE_REF));
		define_builtin_ident(&mut scope, "open_ok", Def::Enum(EnumRef(*FILE_OPEN_STATUS_TYPE_REF, 0)));
		define_builtin_ident(&mut scope, "status_error", Def::Enum(EnumRef(*FILE_OPEN_STATUS_TYPE_REF, 1)));
		define_builtin_ident(&mut scope, "name_error", Def::Enum(EnumRef(*FILE_OPEN_STATUS_TYPE_REF, 2)));
		define_builtin_ident(&mut scope, "mode_error", Def::Enum(EnumRef(*FILE_OPEN_STATUS_TYPE_REF, 3)));

		scope
	};

	/// All builtin scopes.
	///
	/// These are added to the scoreboard upon construction.
	pub static ref BUILTIN_SCOPES: Vec<(ScopeRef, &'static Scope)> = vec![
		(*ROOT_SCOPE_REF, &*ROOT_SCOPE),
		((*STD_LIB_REF).into(), &*STD_LIB_SCOPE),
		((*STANDARD_PKG_REF).into(), &*STANDARD_PKG_SCOPE),
	];

	/// All builtin types.
	///
	/// These are added to the scoreboard upon construction.
	pub static ref BUILTIN_TYPES: Vec<(TypeDeclRef, Ty)> = vec![
		(*BOOLEAN_TYPE_REF, EnumTy::new(*BOOLEAN_TYPE_REF).into()),
		(*BIT_TYPE_REF, EnumTy::new(*BIT_TYPE_REF).into()),
		(*SEVERITY_LEVEL_TYPE_REF, EnumTy::new(*SEVERITY_LEVEL_TYPE_REF).into()),
		(*INTEGER_TYPE_REF, IntTy::new(Dir::To, i32::min_value().into(), i32::max_value().into()).into()),
		(*NATURAL_TYPE_REF, IntTy::new(Dir::To, 0.into(), i32::max_value().into()).into()),
		(*POSITIVE_TYPE_REF, IntTy::new(Dir::To, 1.into(), i32::max_value().into()).into()),
		(*FILE_OPEN_KIND_TYPE_REF, EnumTy::new(*FILE_OPEN_KIND_TYPE_REF).into()),
		(*FILE_OPEN_STATUS_TYPE_REF, EnumTy::new(*FILE_OPEN_STATUS_TYPE_REF).into()),
	];

	/// All builtin scope references.
	pub static ref BUILTIN_SCOPE_REFS: HashSet<ScopeRef> = (*BUILTIN_SCOPES)
		.iter()
		.map(|&(id,_)| id)
		.collect();
}

/// Add the builtins to a scoreboard.
pub fn register_builtins<'ast, 'ctx>(sb: &ScoreBoard<'ast, 'ctx>) {
	debugln!("registering builtins");

	// Add the builtin scopes.
	sb.scope2_table.borrow_mut().extend((*BUILTIN_SCOPES)
		.iter()
		.map(|&(id, scope)| (id, scope.clone()))
	);

	// Add the builtin types.
	sb.ty_table.borrow_mut().extend((*BUILTIN_TYPES)
		.iter()
		.map(|&(id, ref ty)| (id.into(), sb.intern_ty(ty.clone())))
	);
}
