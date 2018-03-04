// Copyright (c) 2018 Fabian Schuiki

//! Builtin libraries, packages, types, and functions.

use std::collections::HashSet;

use num::BigInt;

use common::score::NodeRef;
use common::source::*;
use common::name::*;

use score::{ResolvableName, ScoreBoard, ScopeRef, LibRef, BuiltinPkgRef, Def, TypeMarkRef, TypeDeclRef, EnumRef, UnitRef};
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
	// A reference to the type `TIME`.
	pub static ref TIME_TYPE_REF: TypeDeclRef = TypeDeclRef::alloc();
	// A reference to the type `DELAY_LENGTH`.
	pub static ref DELAY_LENGTH_TYPE_REF: TypeDeclRef = TypeDeclRef::alloc();
	// A reference to the type `NATURAL`.
	pub static ref NATURAL_TYPE_REF: TypeDeclRef = TypeDeclRef::alloc();
	// A reference to the type `POSITIVE`.
	pub static ref POSITIVE_TYPE_REF: TypeDeclRef = TypeDeclRef::alloc();
	// A reference to the type `BOOLEAN_VECTOR`.
	pub static ref BOOLEAN_VECTOR_TYPE_REF: TypeDeclRef = TypeDeclRef::alloc();
	// A reference to the type `BIT_VECTOR`.
	pub static ref BIT_VECTOR_TYPE_REF: TypeDeclRef = TypeDeclRef::alloc();
	// A reference to the type `INTEGER_VECTOR`.
	pub static ref INTEGER_VECTOR_TYPE_REF: TypeDeclRef = TypeDeclRef::alloc();
	// A reference to the type `TIME_VECTOR`.
	pub static ref TIME_VECTOR_TYPE_REF: TypeDeclRef = TypeDeclRef::alloc();
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

/// Create a named type that refers to a builtin type.
fn named_builtin_type<T: Into<TypeMarkRef>>(name: &str, type_ref: T) -> Ty {
	let name = get_name_table().intern(name, false);
	Ty::Named(name.into(), type_ref.into())
}

/// Create a named physical unit.
fn named_unit(name: &str, abs: usize, rel: Option<(usize, usize)>) -> PhysicalUnit {
	let name = get_name_table().intern(name, false);
	let abs = BigInt::from(abs);
	let rel = rel.map(|(scale, index)| (BigInt::from(scale), index));
	PhysicalUnit::new(name, abs, rel)
}

// Define the scopes of the builtins.
lazy_static! {
	/// The root scope.
	///
	/// It contains definitions equal to `library std; use std.standard.all;`
	pub static ref ROOT_SCOPE: Scope = {
		let mut scope = Scope::new(None);
		define_builtin_ident(&mut scope, "STD", Def::Lib(*STD_LIB_REF));
		scope.imported_scopes.insert((*STANDARD_PKG_REF).into());
		scope
	};

	/// The scope of the library `STD`.
	pub static ref STD_LIB_SCOPE: Scope = {
		let mut scope = Scope::new(Some(*ROOT_SCOPE_REF));
		define_builtin_ident(&mut scope, "STANDARD", Def::BuiltinPkg(*STANDARD_PKG_REF));
		define_builtin_ident(&mut scope, "TEXTIO", Def::BuiltinPkg(*TEXTIO_PKG_REF));
		define_builtin_ident(&mut scope, "ENV", Def::BuiltinPkg(*ENV_PKG_REF));
		scope
	};

	/// The scope of the package `STANDARD`.
	pub static ref STANDARD_PKG_SCOPE: Scope = {
		let mut scope = Scope::new(Some((*STD_LIB_REF).into()));

		// `type BOOLEAN is (FALSE, TRUE)`
		define_builtin_ident(&mut scope, "BOOLEAN", Def::Type(*BOOLEAN_TYPE_REF));
		define_builtin_ident(&mut scope, "FALSE", Def::Enum(EnumRef(*BOOLEAN_TYPE_REF, 0)));
		define_builtin_ident(&mut scope, "TRUE", Def::Enum(EnumRef(*BOOLEAN_TYPE_REF, 1)));

		// `type BIT is ('0', '1')`
		define_builtin_ident(&mut scope, "BIT", Def::Type(*BIT_TYPE_REF));
		define_builtin_bit(&mut scope, '0', Def::Enum(EnumRef(*BIT_TYPE_REF, 0)));
		define_builtin_bit(&mut scope, '1', Def::Enum(EnumRef(*BIT_TYPE_REF, 1)));

		// `type SEVERITY_LEVEL is (NOTE, WARNING, ERROR, FAILURE)`
		define_builtin_ident(&mut scope, "SEVERITY_LEVEL", Def::Type(*SEVERITY_LEVEL_TYPE_REF));
		define_builtin_ident(&mut scope, "NOTE", Def::Enum(EnumRef(*SEVERITY_LEVEL_TYPE_REF, 0)));
		define_builtin_ident(&mut scope, "WARNING", Def::Enum(EnumRef(*SEVERITY_LEVEL_TYPE_REF, 1)));
		define_builtin_ident(&mut scope, "ERROR", Def::Enum(EnumRef(*SEVERITY_LEVEL_TYPE_REF, 2)));
		define_builtin_ident(&mut scope, "FAILURE", Def::Enum(EnumRef(*SEVERITY_LEVEL_TYPE_REF, 3)));

		// `type INTEGER is range ... to ...`
		define_builtin_ident(&mut scope, "INTEGER", Def::Type(*INTEGER_TYPE_REF));

		// `type TIME is range ... to ... units ... end units`
		define_builtin_ident(&mut scope, "TIME", Def::Type(*TIME_TYPE_REF));
		define_builtin_ident(&mut scope, "fs", Def::Unit(UnitRef(*TIME_TYPE_REF, 0)));
		define_builtin_ident(&mut scope, "ps", Def::Unit(UnitRef(*TIME_TYPE_REF, 1)));
		define_builtin_ident(&mut scope, "ns", Def::Unit(UnitRef(*TIME_TYPE_REF, 2)));
		define_builtin_ident(&mut scope, "us", Def::Unit(UnitRef(*TIME_TYPE_REF, 3)));
		define_builtin_ident(&mut scope, "ms", Def::Unit(UnitRef(*TIME_TYPE_REF, 4)));
		define_builtin_ident(&mut scope, "sec", Def::Unit(UnitRef(*TIME_TYPE_REF, 5)));
		define_builtin_ident(&mut scope, "min", Def::Unit(UnitRef(*TIME_TYPE_REF, 6)));
		define_builtin_ident(&mut scope, "hr", Def::Unit(UnitRef(*TIME_TYPE_REF, 7)));

		// `subtype DELAY_LENGTH is TIME range 0 to TIME'HIGH`
		define_builtin_ident(&mut scope, "DELAY_LENGTH", Def::Type(*DELAY_LENGTH_TYPE_REF));

		// `subtype NATURAL is INTEGER range 0 to INTEGER'HIGH`
		define_builtin_ident(&mut scope, "NATURAL", Def::Type(*NATURAL_TYPE_REF));

		// `subtype POSITIVE is INTEGER range 1 to INTEGER'HIGH`
		define_builtin_ident(&mut scope, "POSITIVE", Def::Type(*POSITIVE_TYPE_REF));

		// `type BOOLEAN_VECTOR is array (NATURAL range <>) of BOOLEAN`
		define_builtin_ident(&mut scope, "BOOLEAN_VECTOR", Def::Type(*BOOLEAN_VECTOR_TYPE_REF));

		// `type BIT_VECTOR is array (NATURAL range <>) of BIT`
		define_builtin_ident(&mut scope, "BIT_VECTOR", Def::Type(*BIT_VECTOR_TYPE_REF));

		// `type INTEGER_VECTOR is array (NATURAL range <>) of INTEGER`
		define_builtin_ident(&mut scope, "INTEGER_VECTOR", Def::Type(*INTEGER_VECTOR_TYPE_REF));

		// `type TIME_VECTOR is array (NATURAL range <>) of TIME`
		define_builtin_ident(&mut scope, "TIME_VECTOR", Def::Type(*TIME_VECTOR_TYPE_REF));

		// `type FILE_OPEN_KIND is (READ_MODE, WRITE_MODE, APPEND_MODE)`
		define_builtin_ident(&mut scope, "FILE_OPEN_KIND", Def::Type(*FILE_OPEN_KIND_TYPE_REF));
		define_builtin_ident(&mut scope, "READ_MODE", Def::Enum(EnumRef(*FILE_OPEN_KIND_TYPE_REF, 0)));
		define_builtin_ident(&mut scope, "WRITE_MODE", Def::Enum(EnumRef(*FILE_OPEN_KIND_TYPE_REF, 1)));
		define_builtin_ident(&mut scope, "APPEND_MODE", Def::Enum(EnumRef(*FILE_OPEN_KIND_TYPE_REF, 2)));

		// `type FILE_OPEN_STATUS is (OPEN_OK, STATUS_ERROR, NAME_ERROR, MODE_ERROR)`
		define_builtin_ident(&mut scope, "FILE_OPEN_STATUS", Def::Type(*FILE_OPEN_STATUS_TYPE_REF));
		define_builtin_ident(&mut scope, "OPEN_OK", Def::Enum(EnumRef(*FILE_OPEN_STATUS_TYPE_REF, 0)));
		define_builtin_ident(&mut scope, "STATUS_ERROR", Def::Enum(EnumRef(*FILE_OPEN_STATUS_TYPE_REF, 1)));
		define_builtin_ident(&mut scope, "NAME_ERROR", Def::Enum(EnumRef(*FILE_OPEN_STATUS_TYPE_REF, 2)));
		define_builtin_ident(&mut scope, "MODE_ERROR", Def::Enum(EnumRef(*FILE_OPEN_STATUS_TYPE_REF, 3)));

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
		(*INTEGER_TYPE_REF, IntTy::new(
			Dir::To,
			i32::min_value().into(),
			i32::max_value().into()
		).into()),
		(*TIME_TYPE_REF, make_time_type(
			*TIME_TYPE_REF,
			IntTy::new(
				Dir::To,
				i64::min_value().into(),
				i64::max_value().into(),
			)
		).into()),
		(*DELAY_LENGTH_TYPE_REF, make_time_type(
			*DELAY_LENGTH_TYPE_REF,
			IntTy::new(
				Dir::To,
				0.into(),
				i64::max_value().into(),
			)
		).into()),
		(*NATURAL_TYPE_REF, IntTy::new(
			Dir::To,
			0.into(),
			i32::max_value().into()
		).into()),
		(*POSITIVE_TYPE_REF, IntTy::new(
			Dir::To,
			1.into(),
			i32::max_value().into()
		).into()),
		(*BOOLEAN_VECTOR_TYPE_REF, ArrayTy::new(
			vec![ArrayIndex::Unbounded(Box::new(named_builtin_type("NATURAL", *NATURAL_TYPE_REF)))],
			Box::new(named_builtin_type("BOOLEAN", *BOOLEAN_TYPE_REF))
		).into()),
		(*BIT_VECTOR_TYPE_REF, ArrayTy::new(
			vec![ArrayIndex::Unbounded(Box::new(named_builtin_type("NATURAL", *NATURAL_TYPE_REF)))],
			Box::new(named_builtin_type("BIT", *BIT_TYPE_REF))
		).into()),
		(*INTEGER_VECTOR_TYPE_REF, ArrayTy::new(
			vec![ArrayIndex::Unbounded(Box::new(named_builtin_type("NATURAL", *NATURAL_TYPE_REF)))],
			Box::new(named_builtin_type("INTEGER", *INTEGER_TYPE_REF))
		).into()),
		(*TIME_VECTOR_TYPE_REF, ArrayTy::new(
			vec![ArrayIndex::Unbounded(Box::new(named_builtin_type("NATURAL", *NATURAL_TYPE_REF)))],
			Box::new(named_builtin_type("TIME", *TIME_TYPE_REF))
		).into()),
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

/// Create a physical type with time units.
fn make_time_type(decl: TypeDeclRef, base: IntTy) -> PhysicalTy {
	PhysicalTy::new(
		decl,
		base,
		vec![
			named_unit("fs",  1,                        None            ),
			named_unit("ps",  1_000,                    Some((1000, 0)) ),
			named_unit("ns",  1_000_000,                Some((1000, 1)) ),
			named_unit("us",  1_000_000_000,            Some((1000, 2)) ),
			named_unit("ms",  1_000_000_000_000,        Some((1000, 3)) ),
			named_unit("sec", 1_000_000_000_000_000,    Some((1000, 4)) ),
			named_unit("min", 60_000_000_000_000_000,   Some((60, 5))   ),
			named_unit("hr",  3600_000_000_000_000_000, Some((60, 6))   ),
		],
		0
	)
}
