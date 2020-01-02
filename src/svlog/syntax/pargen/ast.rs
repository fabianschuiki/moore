#[derive(Default, Debug)]
pub struct Grammar {
    pub nts: Vec<Nonterminal>,
}

#[derive(Default, Debug)]
pub struct Nonterminal {
    pub name: String,
    pub prods: Vec<Production>,
}

#[derive(Default, Debug)]
pub struct Production {
    pub syms: Vec<Symbol>,
}

#[derive(Debug)]
pub enum Symbol {
    Token(String),
    Maybe(Vec<Symbol>),
    Any(Vec<Symbol>),
    Some(Vec<Symbol>),
}
