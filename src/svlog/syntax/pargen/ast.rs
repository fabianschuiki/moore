#[derive(Default, Debug)]
pub struct Grammar {
    pub nts: Vec<Nonterminal>,
}

#[derive(Default, Debug)]
pub struct Nonterminal {
    pub public: bool,
    pub name: String,
    pub choices: Vec<Vec<Symbol>>,
}

#[derive(Debug)]
pub enum Symbol {
    Epsilon,
    Token(String),
    Group(Vec<Symbol>),
    Maybe(Box<Symbol>),
    Any(Box<Symbol>),
    Some(Box<Symbol>),
}
