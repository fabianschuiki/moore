// Copyright (c) 2016 Fabian Schuiki
use std;
use std::rc::{Rc, Weak};
use std::cell::{Cell,RefCell,Ref};
use std::cmp::{PartialEq, Eq, PartialOrd, Ord, Ordering};
use std::collections::HashMap;
use std::fmt::Debug;


/// A parsed grammar file.
pub struct Grammar<'a> {
	rules: Vec<Box<Rule<'a>>>,
	rules_by_name: HashMap<Box<str>, &'a Rule<'a>>,
	root: &'a Rule<'a>,
	terminals: HashMap<Box<str>, Box<str>>,
}

/// An individual rule within a grammar. A rule consists of multiple variants,
/// or productions.
pub struct Rule<'a> {
	id: usize,
	// grammar: Weak<RefCell<Grammar>>,
	grammar: Cell<&'a Grammar<'a>>,
	name: Box<str>,
	// variants: Vec<Rc<RefCell<Variant>>>,
	variants: Vec<Box<Variant<'a>>>,
	// retype: Option<Box<str>>,
	reduced_type: Option<Box<str>>,
}

/// A variant or production of a rule.
pub struct Variant<'a> {
	id: usize,
	// rule: Weak<RefCell<Rule>>,
	rule: Cell<&'a Rule<'a>>,
	symbols: Vec<Symbol<'a>>,
	// reducer: Option<Box<str>>,
	reducer_fn: Option<Box<str>>,
}

#[derive(Clone)]
pub enum Symbol<'a> {
	End,
	Unresolved(Box<str>),
	Terminal(Box<str>),
	// NonTerminal(Weak<RefCell<Rule>>),
	NonTerminal(&'a Rule<'a>),
}

type RulesIterator<'a,'b> = std::slice::Iter<'b, Box<Rule<'a>>>;
type VariantsIterator<'a,'b> = std::slice::Iter<'b, Box<Variant<'a>>>;
type SymbolsIterator<'a,'b> = std::slice::Iter<'b, Symbol<'a>>;


impl<'a> Grammar<'a> {
	// pub fn link(&self) {
	// 	// Build a rule lookup table.
	// 	let rule_table = {
	// 		let mut tbl = HashMap::<Box<str>, Weak<RefCell<Rule>>>::new();
	// 		for rule in &self.rules {
	// 			tbl.insert(rule.borrow().name.clone(), Rc::downgrade(&rule));
	// 		}
	// 		tbl
	// 	};

	// 	// Link the symbols.
	// 	let mut id = 0;
	// 	for rule_cell in &self.rules {
	// 		let mut rule = rule_cell.borrow_mut();
	// 		rule.id = id;
	// 		id += 1;

	// 		for variant_cell in &rule.variants {
	// 			let mut variant = variant_cell.borrow_mut();
	// 			variant.id = id;
	// 			id += 1;

	// 			for symbol in &variant.symbols {
	// 				let replacement =
	// 					if let Symbol::Unresolved(ref name) = *symbol.borrow() {
	// 						if let Some(rule) = rule_table.get(name.as_str()) {
	// 							Symbol::NonTerminal(rule.clone())
	// 						} else {
	// 							Symbol::Terminal(name.clone())
	// 						}
	// 					} else {
	// 						continue;
	// 					};
	// 				*symbol.borrow_mut() = replacement;
	// 			}
	// 		}
	// 	}
	// }

	// rules
	// root

	pub fn rules<'b>(&'b self) -> RulesIterator<'a,'b> {
		self.rules.iter()
	}

	pub fn get_root(&self) -> &'a Rule<'a> {
		self.root
	}

	// pub fn get_root(&self) -> &Rc<RefCell<Rule>> {
	// 	assert!(self.rules.len() > 0);
	// 	return &self.rules[0];
	// }

	pub fn get_pattern(&self, name: &str) -> String {
		// let mut s = String::from("Token::");
		// match name {
		// 	"IDENT" => s.push_str("Ident(_)"),
		// 	"LPAREN" => s.push_str("Symbol(Symbol::LParen)"),
		// 	"RPAREN" => s.push_str("Symbol(Symbol::RParen)"),
		// 	"LBRACE" => s.push_str("Symbol(Symbol::LBrace)"),
		// 	"RBRACE" => s.push_str("Symbol(Symbol::RBrace)"),
		// 	"LBRACK" => s.push_str("Symbol(Symbol::LBrack)"),
		// 	"RBRACK" => s.push_str("Symbol(Symbol::RBrack)"),
		// 	"SUFFIX" => s.push_str("Ident(_)"),
		// 	"SEMICOLON"|"COMMA"|"COLON"|"PERIOD" => {
		// 		s.push_str("Symbol(Symbol::");
		// 		let mut it = name.chars();
		// 		if let Some(c) = it.next() {
		// 			s.push(c.to_uppercase().next().unwrap());
		// 		}
		// 		while let Some(c) = it.next() {
		// 			s.push(c.to_lowercase().next().unwrap());
		// 		}
		// 		s.push_str(")");
		// 	},
		// 	_ => {
		// 		s.push_str("Keyword(Keyword::");
		// 		let mut it = name.chars();
		// 		if let Some(c) = it.next() {
		// 			s.push(c.to_uppercase().next().unwrap());
		// 		}
		// 		while let Some(c) = it.next() {
		// 			s.push(c.to_lowercase().next().unwrap());
		// 		}
		// 		s.push_str(")");
		// 	}
		// }
		// return s
		// return name.into();
		match self.terminals.get(name) {
			Some(x) => String::from(x.as_ref()),
			None => panic!("Unknown terminal \"{}\"", name)
		}
	}
}

impl<'a> Debug for Grammar<'a> {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		for rule in &self.rules {
			try!(write!(f, "{:?}\n", rule));
		}
		Ok(())
	}
}



// -----------------------------------------------------------------------------
// Rule
// -----------------------------------------------------------------------------

impl<'a> Rule<'a> {
	// id
	// grammar
	// name
	// variants
	// reduced_type

	pub fn get_id(&self) -> usize {
		self.id
	}

	pub fn get_grammar(&self) -> &'a Grammar<'a> {
		self.grammar.get()
	}

	pub fn get_name(&self) -> &str {
		self.name.as_ref()
	}

	pub fn variants<'b>(&'b self) -> VariantsIterator<'a,'b> {
		self.variants.iter()
	}

	pub fn get_reduced_type(&self) -> Option<&Box<str>> {
		self.reduced_type.as_ref()
	}

	// pub fn get_variants(&self) -> &Vec<Rc<RefCell<Variant>>> {
	// 	&self.variants
	// }
}

impl<'a> Ord for Rule<'a> {
	fn cmp(&self, other: &Self) -> Ordering {
		// self.id.cmp(&other.id)
		match self.variants.cmp(&other.variants) {
			Ordering::Equal => (),
			o => return o
		}
		return self.reduced_type.cmp(&other.reduced_type);
	}
}

impl<'a> PartialOrd for Rule<'a> {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl<'a> PartialEq for Rule<'a> {
	fn eq(&self, other: &Self) -> bool {
		// self.id == other.id
		self.cmp(&other) == Ordering::Equal
	}
}

impl<'a> Eq for Rule<'a> {}

impl<'a> Debug for Rule<'a> {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		try!(write!(f, "{}", self.name));
		let mut sep = ':';
		for variant in &self.variants {
			try!(write!(f, "\n    {} {:?}", sep, variant));
			sep = '|';
		}
		write!(f, " ;")
	}
}



// -----------------------------------------------------------------------------
// Variant
// -----------------------------------------------------------------------------

impl<'a> Variant<'a> {
	// id
	// rule
	// symbols
	// reducer_fn

	pub fn get_id(&self) -> usize {
		self.id
	}

	pub fn get_rule(&self) -> &'a Rule<'a> {
		self.rule.get()
	}

	pub fn symbols<'b>(&'b self) -> SymbolsIterator<'a,'b> {
		// SymbolsIterator { r: self.symbols.borrow(), it: self.symbols.borrow().iter() }
		self.symbols.iter()
	}

	pub fn get_symbol(&self, idx: usize) -> &Symbol<'a> {
		&self.symbols[idx]
	}

	// pub fn get_symbols(&self) -> &'a Vec<RefCell<Symbol<'a>>> {
	// 	&self.symbols
	// }

	pub fn get_reducer_fn(&self) -> Option<&Box<str>> {
		self.reducer_fn.as_ref()
	}
}

impl<'a> Ord for Variant<'a> {
	fn cmp(&self, other: &Self) -> Ordering {
		// self.id.cmp(&other.id)
		match (self.get_rule() as *const _).cmp(&(other.get_rule() as *const _)) {
			Ordering::Equal => (),
			o => return o
		}
		match self.symbols.cmp(&other.symbols) {
			Ordering::Equal => (),
			o => return o
		}
		return self.reducer_fn.cmp(&other.reducer_fn);
	}
}

impl<'a> PartialOrd for Variant<'a> {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl<'a> PartialEq for Variant<'a> {
	fn eq(&self, other: &Self) -> bool {
		// self.id == other.id
		self.cmp(&other) == Ordering::Equal
	}
}

impl<'a> Eq for Variant<'a> {}

impl<'a> Debug for Variant<'a> {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		let mut it = self.symbols();
		if let Some(sym) = it.next() {
			try!(sym.fmt(f));
			for sym in it {
				try!(write!(f, " "));
				try!(sym.fmt(f));
			}
		}
		Ok(())
	}
}



// -----------------------------------------------------------------------------
// Symbol
// -----------------------------------------------------------------------------

impl<'a> Symbol<'a> {
	fn cardinal(&self) -> u32 {
		match *self {
			Symbol::End => 0,
			Symbol::Unresolved(_) => 1,
			Symbol::Terminal(_) => 2,
			Symbol::NonTerminal(_) => 3,
		}
	}

	fn get_name(&self) -> &str {
		match *self {
			Symbol::Unresolved(ref name) => name,
			Symbol::Terminal(ref name) => name,
			_ => panic!("{:?} has no name", self),
		}
	}

	fn get_rule(&self) -> &Rule<'a> {
		match *self {
			Symbol::NonTerminal(rule) => rule,
			_ => panic!("{:?} has no rule", self),
		}
	}
}

impl<'a> Ord for Symbol<'a> {
	fn cmp(&self, other: &Self) -> Ordering {
		let o = self.cardinal().cmp(&other.cardinal());
		if o == Ordering::Equal {
			match *self {
				Symbol::Unresolved(ref name) => name.as_ref().cmp(other.get_name()),
				Symbol::Terminal(ref name) => name.as_ref().cmp(other.get_name()),
				Symbol::NonTerminal(rule) => rule.get_id().cmp(&other.get_rule().get_id()),
				_ => o,
			}
		} else {
			o
		}
	}
}

impl<'a> PartialOrd for Symbol<'a> {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl<'a> PartialEq for Symbol<'a> {
	fn eq(&self, other: &Self) -> bool {
		self.cmp(other) == Ordering::Equal
	}
}

impl<'a> Eq for Symbol<'a> {}

impl<'a> Debug for Symbol<'a> {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match *self {
			Symbol::Unresolved(ref x) => write!(f, "<?'{}'>", x),
			Symbol::Terminal(ref x) => write!(f, "{}", x),
			Symbol::NonTerminal(rule) => {
				return write!(f, "{}", rule.get_name());
			},
			Symbol::End => write!(f, "$"),
		}
	}
}


#[derive(Debug)]
pub struct GrammarBuilder {
	terminals: HashMap<Box<str>, Box<str>>,
	rule_builders: Vec<RuleBuilder>,
	root: Option<Box<str>>,
}

#[derive(Debug)]
pub struct RuleBuilder {
	grammar: *mut GrammarBuilder,
	name: Box<str>,
	variant_builders: Vec<VariantBuilder>,
	reduced_type: Option<Box<str>>,
}

#[derive(Debug)]
pub struct VariantBuilder {
	rule: *mut RuleBuilder,
	symbols: Vec<Box<str>>,
	reducer_fn: Option<Box<str>>,
}

impl GrammarBuilder {
	pub fn new() -> GrammarBuilder {
		GrammarBuilder {
			terminals: HashMap::new(),
			rule_builders: Vec::new(),
			root: None,
		}
	}

	pub fn add_terminal(&mut self, name: Box<str>, pattern: Box<str>) {
		self.terminals.insert(name, pattern);
	}

	pub fn new_rule(&mut self, name: Box<str>) -> RuleBuilder {
		RuleBuilder {
			grammar: self,
			name: name,
			variant_builders: Vec::new(),
			reduced_type: None,
		}
	}

	pub fn set_root(&mut self, name: Box<str>) {
		self.root = Some(name);
	}

	pub fn build<'a>(self) -> Box<Grammar<'a>> {
		let mut grammar = Box::new(Grammar {
			rules: Vec::new(),
			rules_by_name: HashMap::new(),
			terminals: self.terminals,
			root: unsafe { &*(0 as *const Rule<'a>) },
		});

		let mut root_rule = None;
		let root_name = self.root.expect("No root rule has been specified");
		let mut rule_id = 0;
		let mut variant_id = 0;
		let mut symbols_by_variant = HashMap::<*const Variant, Vec<Box<str>>>::new();

		for rb in self.rule_builders {
			rule_id += 1;
			println!("processing rule builder {}: {:?}", rule_id, rb);
			let mut rule = Box::new(Rule {
				id: rule_id,
				grammar: Cell::new(unsafe { &*(grammar.as_ref() as *const Grammar<'a>) }),
				name: rb.name,
				variants: Vec::new(),
				reduced_type: rb.reduced_type,
			});

			// Check if this is the root rule and keep a reference around if it
			// is. Use an unsafe block here to stop the borrow checker from
			// whining since we guarantee that the pointed-to rule lives as long
			// as the containing grammar lives anyway.
			if root_name == rule.name {
				assert!(root_rule.is_none(), "Root rule \"{}\" is defined multiple times", root_name);
				root_rule = Some(unsafe { &*(rule.as_ref() as *const Rule) });
			}

			// Build the variants contained within this rule.
			for vb in rb.variant_builders {
				variant_id += 1;
				println!("processing variant builder {}: {:?}",  variant_id, vb);
				let mut variant = Box::new(Variant {
					id: variant_id,
					rule: Cell::new(unsafe { &*(rule.as_ref() as *const Rule<'a>) }),
					symbols: Vec::new(),
					reducer_fn: vb.reducer_fn,
				});
				symbols_by_variant.insert(variant.as_ref(), vb.symbols);

				// Add the variant to the list.
				rule.variants.push(variant);
			}

			// Add the rule to the list.
			grammar.rules.push(rule);
		}

		// Make a lookup table of rules.
		let mut rules_by_name = HashMap::new();
		for rule in &grammar.rules {
			let result = rules_by_name.insert(
				rule.get_name().to_string().into_boxed_str(),
				unsafe { &*(rule.as_ref() as *const Rule) },
			);
			if let Some(existing) = result {
				panic!("Multiple definitions of rule \"{}\". The old rule was: {:?}", rule.get_name(), existing);
			}
		}

		// Resolve the symbol references.
		for rule in &mut grammar.rules {
			for variant in &mut rule.variants {
				variant.symbols = symbols_by_variant
					.get_mut(&(variant.as_ref() as *const Variant))
					.unwrap()
					.drain(..)
					.map(|x| {
						if let Some(rule) = rules_by_name.get(x.as_ref()) {
							Symbol::NonTerminal(rule)
						} else {
							Symbol::Terminal(x)
						}
					}).collect();
			}
		}
		grammar.rules_by_name = rules_by_name;

		// Ensure that we have actually found the root rule.
		if root_rule.is_none() {
			panic!("Root rule \"{}\" has not been defined", root_name);
		} else {
			grammar.root = root_rule.unwrap();
			println!("The root rule is {:?}", grammar.root);
		}

		grammar
	}
}

impl RuleBuilder {
	pub fn new_variant(&mut self) -> VariantBuilder {
		VariantBuilder {
			rule: self,
			symbols: Vec::new(),
			reducer_fn: None,
		}
	}

	pub fn set_reduced_type(&mut self, ty: Box<str>) {
		self.reduced_type = Some(ty);
	}

	pub fn build(self) {
		unsafe { (*(self.grammar as *mut GrammarBuilder)).rule_builders.push(self); }
	}
}

impl VariantBuilder {
	pub fn add_symbol(&mut self, sym: Box<str>) {
		self.symbols.push(sym);
	}

	pub fn set_reducer_fn(&mut self, fname: Box<str>) {
		self.reducer_fn = Some(fname);
	}

	pub fn build(self) {
		unsafe { (*(self.rule as *mut RuleBuilder)).variant_builders.push(self); }
	}
}



/// A wrapper around a borrowed RefCell that contains a vector. This allows an
/// iterator to the vector to be returned, by wrapping and returning the Ref to
/// the caller, thus ensuring it has sufficient lifetime.
struct VecRefWrapper<'a, T: 'a> {
	r: Ref<'a, Vec<T>>
}

impl<'a, 'b: 'a, T: 'a> IntoIterator for &'b VecRefWrapper<'a, T> {
	type IntoIter = std::slice::Iter<'a, T>;
	type Item = &'a T;

	fn into_iter(self) -> std::slice::Iter<'a, T> {
		self.r.iter()
	}
}



// A symbol iterator that also holds a Ref to the vector of symbols. This is
// necessary since the symbols are listed in a RefCell<Vec<...>>, and must
// therefore be accessed through a Ref<Vec<...>> at runtime.
// struct SymbolsIterator<'tr, 'tg: 'tr> {
// 	r: Ref<'tr, Vec<Symbol<'tg>>>,
// 	it: std::slice::Iter<'tr, Symbol<'tg>>,
// }

// impl<'tr,'tg> Iterator for SymbolsIterator<'tr,'tg> {
// 	type Item = Symbol<'tg>;

// 	fn next(&mut self) -> Option<Symbol<'tg>> {

// 	}
// }
