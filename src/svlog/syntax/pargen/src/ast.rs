#[derive(Default, Debug)]
pub struct Grammar {
    pub nts: Vec<Nonterminal>,
}

#[derive(Default, Debug, PartialEq, Eq, Hash)]
pub struct Nonterminal {
    pub public: bool,
    pub name: String,
    pub choices: Vec<Vec<Symbol>>,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Symbol {
    Epsilon,
    Token(String),
    Group(Vec<Symbol>),
    Choice(Vec<Vec<Symbol>>),
    Maybe(Box<Symbol>),
    Any(Box<Symbol>),
    Some(Box<Symbol>),
}
