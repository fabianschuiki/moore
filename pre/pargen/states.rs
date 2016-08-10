// Copyright (c) 2016 Fabian Schuiki
use std;
use std::rc::{Rc};
use std::cell::{RefCell};
use std::collections::{BTreeSet, BTreeMap};
use std::fmt;
use pargen::grammar::{Grammar, Rule, Variant, Symbol};


pub fn translate<'a>(grammar: &Grammar) -> Vec<Box<State>> {

	let mut states = Vec::new();
	let mut states_head = 0;
	let mut states_by_leads = BTreeMap::new();

	// Create the initial state.
	states.push({
		let mut initial = Box::new(State::new());
		let root = grammar.get_root();
		for v in root.borrow().get_variants() {
			let mut follow = BTreeSet::new();
			follow.insert(Symbol::End);
			initial.add(Lead { rule: root.clone(), variant: v.clone(), pos: 0, follow: follow });
		}

		// println!("Initial State: {:?}", &initial);
		initial.close();
		// println!("Closed: {:?}", &initial);
		initial
	});

	// Keep processing new states as they are generated.
	while states_head < states.len() {
		let mut state = std::mem::replace(&mut states[states_head], Box::new(State::new()));
		// println!("");
		// println!("\n----- STATE {} -----", state.id);

		// Calculate the next states, one for each token consumed, by advancing each
		// lead's pointer one position.
		let mut next_states = BTreeMap::new();
		let mut reduce_map = BTreeMap::new();
		for lead in &state.leads {

			// If there are tokens left in this lead, move over the next,
			// creating new states for the shifted token and populating them
			// with leads.
			if !lead.is_at_end() {
				let sym = lead.get_next(0);
				if !next_states.contains_key(&sym) {
					next_states.insert(sym.clone(), Box::new(State::new()));
				}
				let mut next_lead = lead.clone();
				next_lead.pos += 1;
				next_states.get_mut(&sym).unwrap().add(next_lead);
			}

			// If there are no tokens left, the symbols in the follow set of
			// this lead trigger a reduction.
			else {
				for f in &lead.follow {
					if let Some(other) = reduce_map.get(f) {
						panic!(
							"Reduce-Reduce conflict between {:?} and {:?}; in state {:?}",
							other,
							lead,
							state
						);
					}
					reduce_map.insert(f.clone(), lead.variant.clone());
				}
			}
		}

		// Calcualte the closure of the next states.
		for (_, state) in &mut next_states {
			state.close();
		}
		// println!("Next States: {:?}", &next_states);
		// println!("Reduce: {:?}", &reduce_map);

		// Ensure that there are no shift-reduce conflicts and populate the
		// current state with reduce actions.
		for (sym, variant) in reduce_map {
			if let Some(other) = next_states.get(&sym) {
				panic!(
					"Shift-Reduce conflict between shifting {:?} to arrive at {:?}\nor reducing\n\t{:?};\nin state {:?}",
					sym,
					other,
					variant,
					state
				);
			}
			state.actions.insert(sym, Action::Reduce(variant));
		}

		// Move the next states into the states array if they do not yet exist,
		// and populate the current state's action table.
		// let num_states_before = states.len();
		for (sym, mut next_state) in next_states {
			let state_id = {
				if states_by_leads.contains_key(&next_state.leads) {
					*states_by_leads.get(&next_state.leads).unwrap()
				} else {
					let id = states.len() as u32;
					next_state.id = id;
					states_by_leads.insert(next_state.leads.clone(), id);
					states.push(next_state);
					id
				}
			};

			// Insert the appropriate action.
			let action = match sym {
				Symbol::NonTerminal(_) => Action::Goto(state_id),
				Symbol::Terminal(_) => Action::Shift(state_id),
				_ => panic!("Unexpected symbol {:?}", sym),
			};
			state.actions.insert(sym, action);
		}

		// println!("Actions: {:?}", state.actions);
		// println!("Added {} states", states.len() - num_states_before);

		// Hand the state back to the array.
		std::mem::replace(&mut states[states_head], state);
		states_head += 1;
	}

	states
}


#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Lead {
	rule: Rc<RefCell<Rule>>,
	variant: Rc<RefCell<Variant>>,
	pos: usize,
	follow: SymbolSet,
}

pub struct State {
	pub id: u32,
	pub leads: BTreeSet<Lead>,
	pub actions: BTreeMap<Symbol, Action>,
}

type SymbolSet = BTreeSet<Symbol>;

#[derive(Debug)]
pub enum Action {
	Shift(u32),
	Goto(u32),
	Reduce(Rc<RefCell<Variant>>),
}


impl Lead {
	fn get_next(&self, off: usize) -> Symbol {
		let ref v = *self.variant.borrow();
		let ref s = *v.get_symbols()[self.pos+off].borrow();
		s.clone()
	}

	fn is_at_end(&self) -> bool {
		self.pos == self.variant.borrow().get_symbols().len()
	}

	fn make_follow_set(&self) -> SymbolSet {
		let ref v = *self.variant.borrow();
		let syms = v.get_symbols();
		let num_syms = syms.len();

		let mut first = SymbolSet::new();
		let mut contained_epsilon = true;
		let mut pos = self.pos+1;

		while contained_epsilon && pos < num_syms {
			let mut rules_seen = BTreeSet::new();
			let sym = syms[pos].borrow().clone();

			if let Symbol::NonTerminal(rule_weak) = sym {
				let rule = rule_weak.upgrade().unwrap();
				contained_epsilon = gather_first(&mut first, &rule.borrow(), &mut rules_seen);
			} else {
				first.insert(sym);
				contained_epsilon = false;
			}

			pos += 1;
		}

		// If the last symbol has been reached and its first set still contained
		// epislon, append this lead's follow set.
		if contained_epsilon && pos == num_syms {
			for f in &self.follow {
				first.insert(f.clone());
			}
		}

		first
	}
}


fn gather_first(first: &mut SymbolSet, rule: &Rule, seen: &mut BTreeSet<Rc<RefCell<Rule>>>) -> bool {
	let vars = rule.get_variants();
	if vars.is_empty() {
		return true;
	}

	let mut any_epsilon = false;
	for variant_cell in vars {
		let mut pos: usize = 0;
		let mut epsilon = true;
		let variant = variant_cell.borrow();
		let syms = variant.get_symbols();

		while pos < syms.len() && epsilon == true {
			let sym = syms[pos].borrow();
			match *sym {
				Symbol::NonTerminal(ref rule_weak) => {
					let rule = rule_weak.upgrade().unwrap();
					if !seen.contains(&rule) {
						seen.insert(rule.clone());
						epsilon = gather_first(first, &rule.borrow(), seen);
					} else {
						epsilon = false;
					}
				}
				_ => {
					first.insert(sym.clone());
					epsilon = false;
				}
			}
			pos += 1;
		}

		if epsilon {
			any_epsilon = true;
		}
	}

	return any_epsilon;
}


impl State {
	fn new() -> Self {
		State {
			id: 0,
			leads: BTreeSet::new(),
			actions: BTreeMap::new(),
		}
	}

	fn add(&mut self, lead: Lead) {
		self.leads.insert(lead);
	}

	fn close(&mut self) {
		loop {
			let mut new_states = Vec::new();

			for lead in &self.leads {
				let num_syms = lead.variant.borrow().get_symbols().len();
				if lead.pos < num_syms {
					let next = lead.get_next(0);
					if let Symbol::NonTerminal(ref rule_weak) = next {
						let rule = rule_weak.upgrade().unwrap();
						let follow = lead.make_follow_set();
						if follow.len() == 0 {
							panic!("For symbol {:?}, lead produced empty follow set: {:?}, in state {:?}", next, lead, self);
						}
						for v in rule.borrow().get_variants() {
							let lead = Lead {
								rule: rule.clone(),
								variant: v.clone(),
								pos: 0,
								follow: follow.clone()
							};
							if !self.leads.contains(&lead) {
								new_states.push(lead);
							}
						}
					}
				}
			}

			if new_states.len() == 0 {
				break;
			} else {
				for s in new_states {
					self.leads.insert(s);
				}
			}
		}

		self.compact();
	}

	/// Merges leads in the set which only differ in their follow sets.
	fn compact(&mut self) {
		// TODO: Implement this such that it operates on current_states inplace.
		//       Maybe that's not even possible in Rust.
		let current_states = std::mem::replace(&mut self.leads, BTreeSet::new());
		let mut base: Option<Lead> = None;
		for lead in current_states {
			base =
				if let Some(mut b) = base {
					if b.rule == lead.rule && b.variant == lead.variant && b.pos == lead.pos {
						for f in lead.follow {
							b.follow.insert(f);
						}
						Some(b)
					} else {
						self.leads.insert(b);
						Some(lead)
					}
				} else {
					Some(lead)
				};
		}
		if let Some(lead) = base {
			self.leads.insert(lead);
		}
	}
}


impl fmt::Debug for Lead {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		try!(write!(f, "[{} → ", self.rule.borrow().get_name()));
		let mut i = 0;
		for sym in self.variant.borrow().get_symbols() {
			if self.pos == i {
				try!(write!(f, ". "));
			}
			i += 1;
			try!(write!(f, "{:?} ", sym.borrow()));
		}
		if self.pos == i {
			try!(write!(f, ". "));
		}
		write!(f, "; {:?}]", self.follow)
	}
}

impl fmt::Debug for State {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		try!(write!(f, "{{"));
		let mut it = self.leads.iter();
		if let Some(ref lead) = it.next() {
			try!(write!(f, "\n    {:?}\n", lead));
			for lead in it {
				try!(write!(f, "    {:?}\n", lead));
			}
		}
		write!(f, "}}")
	}
}
