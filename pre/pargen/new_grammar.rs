// Copyright (c) 2016 Fabian Schuiki
use std;
use std::cell::RefCell;
use std::fmt::{Debug, Result, Formatter};

pub struct Grammar {
	terminals: Vec<Terminal>,
	rules: Vec<Rule>,
	variants: Vec<Variant>,
}

#[derive(Debug)]
pub struct Terminal {
	id: usize,
	name: Box<str>,
	ty: Box<str>,
}

pub struct Rule {
	id: usize,
	name: Box<str>,
	variants: (usize,usize),
	reduced_type: Option<Box<str>>,
}

pub struct Variant {
	id: usize,
	rule_id: usize,
	symbols: Vec<Symbol>,
	reducer_fn: Option<Box<str>>,
}

pub enum Symbol {
	End,
	Unresolved(Box<str>),
	Terminal(TerminalRef),
	NonTerminal(RuleRef),
}

type SymbolCell = RefCell<Symbol>;

#[derive(Debug, Clone, Copy)]
pub struct TerminalRef(usize);

#[derive(Debug, Clone, Copy)]
pub struct RuleRef(usize);

#[derive(Debug, Clone, Copy)]
pub struct VariantRef(usize);



impl Grammar {
	pub fn new() -> Self {
		Grammar {
			terminals: Vec::new(),
			rules: Vec::new(),
			variants: Vec::new(),
		}
	}

	/// Add a mapping from a token to a type string to be used in synthesized
	/// Rust code.
	pub fn add_terminal(&mut self, term: Terminal) {
		match self.terminals.binary_search_by(|x| x.name.cmp(&term.name)) {
			Ok(_) => panic!("Terminal {} already defined as {}", term.name, term.ty),
			Err(idx) => self.terminals.insert(idx, term),
		}
	}

	/// Add a rule to the grammar.
	pub fn add_rule(&mut self, rule: Rule) {
		match self.rules.binary_search_by(|x| x.name.cmp(&rule.name)) {
			Ok(_) => panic!("Rule {} already defined", rule.name),
			Err(idx) => self.rules.insert(idx, rule),
		}
	}

	/// Add a variant to the grammar.
	pub fn add_variant(&mut self, mut var: Variant, rule: &mut Rule) {
		var.id = self.variants.len();
		if rule.variants.0 == rule.variants.1 {
			rule.variants.0 = var.id;
		}
		rule.variants.1 = var.id;
		self.variants.push(var);
	}

	/// Assign identifiers to each node in the grammar and resolve references.
	/// Modifying the grammar after this function has been called is an error.
	pub fn link(&mut self) {
		// Assign IDs.
		for (id,term) in self.terminals.iter_mut().enumerate() {
			term.id = id;
		}

		for (rule_id,rule) in self.rules.iter_mut().enumerate() {
			rule.id = rule_id;
			for var_id in rule.variants.0 .. rule.variants.1 {
				self.variants[var_id].rule_id = rule_id
			}
		}

		// Resolve the symbols in the grammar.
		for var in &mut self.variants {
			for sym in &mut var.symbols {
				*sym = match std::mem::replace(sym, Symbol::End) {
					Symbol::Unresolved(ref name) => {
						if let Ok(idx) = self.terminals.binary_search_by(|x| x.name.as_ref().cmp(name)) {
							Symbol::Terminal(TerminalRef(idx))
						} else if let Ok(idx) = self.rules.binary_search_by(|x| x.name.as_ref().cmp(name)) {
							Symbol::NonTerminal(RuleRef(idx))
						} else {
							panic!("Unable to find {}", name);
						}
					},
					x => x
				};
			}
		}
	}
}

impl Debug for Grammar {
	fn fmt(&self, f: &mut Formatter) -> Result {
		for rule in &self.rules {
			try!(write!(f, "{:?}\n", rule));
		}
		Ok(())
	}
}



impl Terminal {
	pub fn new(name: Box<str>, ty: Box<str>) -> Self {
		Terminal {
			id: 0,
			name: name,
			ty: ty,
		}
	}
}



impl Rule {
	pub fn new(name: Box<str>) -> Self {
		Rule {
			id: 0,
			name: name,
			variants: (0,0),
			reduced_type: None,
		}
	}

	pub fn set_reduced_type(&mut self, ty: Box<str>) {
		self.reduced_type = Some(ty);
	}

	pub fn get_name(&self) -> &str {
		self.name.as_ref()
	}
}

impl Debug for Rule {
	fn fmt(&self, f: &mut Formatter) -> Result {
		try!(write!(f, "{} {{", self.name));
		// for variant in &self.variants {
		// 	try!(write!(f, "\n  {:?}", variant));
		// }
		write!(f, "\n}}")
	}
}



impl Variant {
	pub fn new() -> Self {
		Variant {
			id: 0,
			rule_id: 0,
			symbols: Vec::new(),
			reducer_fn: None,
		}
	}

	pub fn set_reducer_fn(&mut self, fname: Box<str>) {
		self.reducer_fn = Some(fname);
	}

	pub fn add_symbol(&mut self, sym: Symbol) {
		self.symbols.push(sym);
	}
}

impl Debug for Variant {
	fn fmt(&self, f: &mut Formatter) -> Result {
		let mut it = self.symbols.iter();
		if let Some(sym) = it.next() {
			try!(sym.fmt(f));
			for sym in it {
				try!(write!(f, " "));
				try!(sym.fmt(f));
			}
		}
		if let Some(ref name) = self.reducer_fn {
			try!(write!(f, " > {}", name));
		}
		write!(f, ";")
	}
}



impl Debug for Symbol {
	fn fmt(&self, f: &mut Formatter) -> Result {
		match self {
			&Symbol::Unresolved(ref x) => write!(f, "<?'{}'>", x),
			&Symbol::Terminal(ref x) => write!(f, "{:?}", x),
			&Symbol::NonTerminal(ref x) => write!(f, "{:?}", x),
			&Symbol::End => write!(f, "$"),
		}
	}
}
