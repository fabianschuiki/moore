// Copyright (c) 2016-2021 Fabian Schuiki

//! A lexical analyzer for SystemVerilog files, based on IEEE 1800-2009, section
//! 5.

use crate::cat::CatTokenKind;
use crate::preproc::*;
pub use crate::token::*;
use moore_common::errors::*;
use moore_common::name::*;
use moore_common::source::*;

type CatTokenAndSpan = (CatTokenKind, Span);
pub type TokenAndSpan = (Token, Span);

/// A lexical analyzer for SystemVerilog files.
pub struct Lexer<'a> {
    input: Preprocessor<'a>,
    peek: [CatTokenAndSpan; 4],
}

impl<'a> Lexer<'a> {
    pub fn new(input: Preprocessor<'a>) -> Lexer {
        Lexer {
            input: input,
            peek: [(CatTokenKind::Eof, INVALID_SPAN); 4],
        }
    }

    pub fn bump(&mut self) -> DiagResult2<()> {
        self.peek[0] = self.peek[1];
        self.peek[1] = self.peek[2];
        self.peek[2] = self.peek[3];
        self.peek[3] = match self.input.next() {
            Some(Err(e)) => return Err(e),
            Some(Ok(x)) => x,
            None => (CatTokenKind::Eof, self.peek[2].1),
        };

        Ok(())
    }

    pub fn next_token(&mut self) -> DiagResult2<TokenAndSpan> {
        // Upon the first invocation the peek buffer is still empty. In that
        // case we need to load the first batch of tokens.
        if self.peek[0].0 == CatTokenKind::Eof {
            self.bump()?;
            self.bump()?;
            self.bump()?;
            self.bump()?;
        }

        let name_table = get_name_table();

        loop {
            self.skip_noise()?;

            // Match 4-character symbols
            if let (
                CatTokenKind::Symbol(c0),
                CatTokenKind::Symbol(c1),
                CatTokenKind::Symbol(c2),
                CatTokenKind::Symbol(c3),
            ) = (
                self.peek[0].0,
                self.peek[1].0,
                self.peek[2].0,
                self.peek[3].0,
            ) {
                let sym = match (c0, c1, c2, c3) {
                    // Assignment
                    ('<', '<', '<', '=') => Some(Operator(Op::AssignArithShL)),
                    ('>', '>', '>', '=') => Some(Operator(Op::AssignArithShR)),
                    _ => None,
                };
                if let Some(tkn) = sym {
                    let sp = Span::union(self.peek[0].1, self.peek[3].1);
                    self.bump()?;
                    self.bump()?;
                    self.bump()?;
                    self.bump()?;
                    return Ok((tkn, sp));
                }
            }

            // Match 3-character symbols
            if let (CatTokenKind::Symbol(c0), CatTokenKind::Symbol(c1), CatTokenKind::Symbol(c2)) =
                (self.peek[0].0, self.peek[1].0, self.peek[2].0)
            {
                let sym = match (c0, c1, c2) {
                    // Assignment
                    ('<', '<', '=') => Some(Operator(Op::AssignLogicShL)),
                    ('>', '>', '=') => Some(Operator(Op::AssignLogicShR)),

                    // Equality
                    ('=', '=', '=') => Some(Operator(Op::CaseEq)),
                    ('!', '=', '=') => Some(Operator(Op::CaseNeq)),
                    ('=', '=', '?') => Some(Operator(Op::WildcardEq)),
                    ('!', '=', '?') => Some(Operator(Op::WildcardNeq)),

                    // Logic
                    ('<', '-', '>') => Some(Operator(Op::LogicEquiv)),

                    // Shift
                    ('<', '<', '<') => Some(Operator(Op::ArithShL)),
                    ('>', '>', '>') => Some(Operator(Op::ArithShR)),

                    // Sequence
                    ('|', '-', '>') => Some(Operator(Op::SeqImplOl)),
                    ('|', '=', '>') => Some(Operator(Op::SeqImplNol)),
                    ('#', '-', '#') => Some(Operator(Op::SeqFollowOl)),
                    ('#', '=', '#') => Some(Operator(Op::SeqFollowNol)),
                    _ => None,
                };
                if let Some(tkn) = sym {
                    let sp = Span::union(self.peek[0].1, self.peek[2].1);
                    self.bump()?;
                    self.bump()?;
                    self.bump()?;
                    return Ok((tkn, sp));
                }
            }

            // Match 2-character symbols
            if let (CatTokenKind::Symbol(c0), CatTokenKind::Symbol(c1)) =
                (self.peek[0].0, self.peek[1].0)
            {
                let sym = match (c0, c1) {
                    // Assignment
                    ('+', '=') => Some(Operator(Op::AssignAdd)),
                    ('-', '=') => Some(Operator(Op::AssignSub)),
                    ('*', '=') => Some(Operator(Op::AssignMul)),
                    ('/', '=') => Some(Operator(Op::AssignDiv)),
                    ('%', '=') => Some(Operator(Op::AssignMod)),
                    ('&', '=') => Some(Operator(Op::AssignBitAnd)),
                    ('|', '=') => Some(Operator(Op::AssignBitOr)),
                    ('^', '=') => Some(Operator(Op::AssignBitXor)),

                    // Arithmetic
                    ('+', '+') => Some(Operator(Op::Inc)),
                    ('-', '-') => Some(Operator(Op::Dec)),
                    ('*', '*') => Some(Operator(Op::Pow)),

                    // Relational
                    ('<', '=') => Some(Operator(Op::Leq)),
                    ('>', '=') => Some(Operator(Op::Geq)),

                    // Logic
                    ('=', '=') => Some(Operator(Op::LogicEq)),
                    ('!', '=') => Some(Operator(Op::LogicNeq)),
                    ('-', '>') => Some(Operator(Op::LogicImpl)),
                    ('|', '|') => Some(Operator(Op::LogicOr)),
                    ('&', '&') => Some(Operator(Op::LogicAnd)),

                    // Bitwise
                    ('~', '&') => Some(Operator(Op::BitNand)),
                    ('~', '|') => Some(Operator(Op::BitNor)),
                    ('~', '^') => Some(Operator(Op::BitNxor)),
                    ('^', '~') => Some(Operator(Op::BitXnor)),

                    // Shift
                    ('<', '<') => Some(Operator(Op::LogicShL)),
                    ('>', '>') => Some(Operator(Op::LogicShR)),

                    // Others
                    (':', ':') => Some(Namespace),
                    ('+', ':') => Some(AddColon),
                    ('-', ':') => Some(SubColon),
                    ('#', '#') => Some(DoubleHashtag),
                    _ => None,
                };
                if let Some(tkn) = sym {
                    let sp = Span::union(self.peek[0].1, self.peek[1].1);
                    self.bump()?;
                    self.bump()?;
                    return Ok((tkn, sp));
                }
            }

            // Match 1-character symbols.
            if let CatTokenKind::Symbol(c0) = self.peek[0].0 {
                let sym = match c0 {
                    // Assignment
                    '=' => Some(Operator(Op::Assign)),

                    // Arithmetic
                    '+' => Some(Operator(Op::Add)),
                    '-' => Some(Operator(Op::Sub)),
                    '*' => Some(Operator(Op::Mul)),
                    '/' => Some(Operator(Op::Div)),
                    '%' => Some(Operator(Op::Mod)),

                    // Relational
                    '<' => Some(Operator(Op::Lt)),
                    '>' => Some(Operator(Op::Gt)),

                    // Logic
                    '!' => Some(Operator(Op::LogicNot)),

                    // Bitwise
                    '~' => Some(Operator(Op::BitNot)),
                    '&' => Some(Operator(Op::BitAnd)),
                    '|' => Some(Operator(Op::BitOr)),
                    '^' => Some(Operator(Op::BitXor)),

                    // Others
                    '(' => Some(OpenDelim(Paren)),
                    ')' => Some(CloseDelim(Paren)),
                    '[' => Some(OpenDelim(Brack)),
                    ']' => Some(CloseDelim(Brack)),
                    '{' => Some(OpenDelim(Brace)),
                    '}' => Some(CloseDelim(Brace)),
                    '#' => Some(Hashtag),
                    ',' => Some(Comma),
                    '.' => Some(Period),
                    ':' => Some(Colon),
                    ';' => Some(Semicolon),
                    '?' => Some(Ternary),
                    '@' => Some(At),
                    _ => None,
                };
                if let Some(tkn) = sym {
                    let sp = self.peek[0].1;
                    self.bump()?;
                    return Ok((tkn, sp));
                }
            }

            match self.peek[0] {
                // A text token either represents an identifier or a number,
                // depending on whether it starts with a digit or a letter. In
                // addition to that, underscores '_' also introduce an
                // identifier. In case the identifier corresponds to a keyword,
                // we emit a separate `Keyword(...)` token.
                // IEEE 1800-2009 5.6 Identifiers
                // IEEE 1800-2009 5.6.2 Keywords
                (CatTokenKind::Text, _) | (CatTokenKind::Symbol('_'), _) => {
                    let (m, msp) = self.match_ident()?;
                    return match find_keyword(&m) {
                        Some(Kw::Begin) => Ok((OpenDelim(Bgend), msp)),
                        Some(Kw::End) => Ok((CloseDelim(Bgend), msp)),
                        Some(kw) => Ok((Keyword(kw), msp)),
                        None => Ok((Ident(name_table.intern(&m, true)), msp)),
                    };
                }

                // System tasks and system functions start with the dollar sign
                // '$', after which all regular identifier characters are
                // allowed.
                // IEEE 1800-2009 5.6.3 System tasks and system functions
                (CatTokenKind::Symbol('$'), sp) => {
                    self.bump()?;
                    return match self.peek[0].0 {
                        CatTokenKind::Text
                        | CatTokenKind::Digits
                        | CatTokenKind::Symbol('_')
                        | CatTokenKind::Symbol('$') => {
                            let (m, msp) = self.match_ident()?;
                            Ok((SysIdent(name_table.intern(&m, true)), Span::union(sp, msp)))
                        }
                        _ => Ok((Dollar, sp)),
                    };
                }

                // Escaped identifiers are introduced with a backslash and last
                // until the next whitespace or newline character.
                // IEEE 1800-2009 5.6.1 Escaped identifiers
                (CatTokenKind::Symbol('\\'), mut sp) => {
                    let mut s = String::new();
                    loop {
                        self.bump()?;
                        if self.peek[0].0 == CatTokenKind::Whitespace
                            || self.peek[0].0 == CatTokenKind::Newline
                            || self.peek[0].0 == CatTokenKind::Eof
                        {
                            break;
                        }
                        sp.expand(self.peek[0].1);
                        s.push_str(&self.peek[0].1.extract());
                    }
                    if s.is_empty() {
                        return Err(DiagBuilder2::fatal(
                            "Expected escaped identifier after backslash '\\'",
                        )
                        .span(sp));
                    }
                    return Ok((EscIdent(name_table.intern(&s, true)), sp));
                }

                // Numbers are either introduced by a set of digits in the case
                // of a sized literal or unsigned number, or an apostrophe in
                // the case of an unsized based number.
                // IEEE 1800-2009 5.7 Numbers
                (CatTokenKind::Symbol('\''), sp) => {
                    self.bump()?; // eat the apostrophe
                    return self.match_based_number(None, sp);
                }
                (CatTokenKind::Digits, mut sp) => {
                    // Consume the leading digits. These represent either the
                    // size of the literal if followed by an apostrophe and a
                    // base specification, or the number itself otherwise.
                    let value = {
                        let mut s = String::new();
                        s.push_str(&sp.extract());
                        self.bump()?; // eat the digits that were pushed onto the string above
                        self.eat_number_body_into(&mut s, &mut sp, false)?;
                        name_table.intern(&s, true)
                    };
                    let frac = if self.peek[0].0 == CatTokenKind::Symbol('.') {
                        let mut s = String::new();
                        self.bump()?; // eat the period
                        self.eat_number_body_into(&mut s, &mut sp, false)?;
                        Some(name_table.intern(&s, true))
                    } else {
                        None
                    };
                    if let Some(unit) = self.try_time_unit() {
                        sp.expand(self.peek[0].1);
                        self.bump()?; // eat the unit
                        return Ok((Literal(Time(value, frac, unit)), sp));
                    }
                    if self.peek[0].0 == CatTokenKind::Text {
                        return Err(DiagBuilder2::fatal(format!(
                            "number literal `{}` may not directly be followed by letters `{}`",
                            sp.extract(),
                            self.peek[0].1.extract(),
                        ))
                        .span(sp));
                    }
                    if frac.is_some() {
                        return Ok((Literal(Number(value, frac)), sp));
                    }
                    self.skip_noise()?; // whitespace allowed after size indication
                    match (self.peek[0].0, self.peek[1].0) {
                        (CatTokenKind::Symbol('\''), CatTokenKind::Text)
                        | (CatTokenKind::Symbol('\''), CatTokenKind::Digits) => {
                            self.bump()?; // eat the apostrophe
                            return self.match_based_number(Some(value), sp);
                        }
                        _ => return Ok((Literal(Number(value, None)), sp)),
                    }
                }

                // IEEE 1800-2009 5.9 String literals
                (CatTokenKind::Symbol('"'), mut span) => {
                    self.bump()?;
                    let mut s = String::new();
                    loop {
                        match self.peek[0] {
                            (CatTokenKind::Symbol('"'), sp) => {
                                span.expand(sp);
                                self.bump()?;
                                break;
                            }
                            (CatTokenKind::Symbol('\\'), sp) => {
                                span.expand(sp);
                                self.bump()?;
                                match self.peek[0] {
                                    (CatTokenKind::Symbol('\\'), sp) => {
                                        span.expand(sp);
                                        s.push('\\');
                                    }
                                    (CatTokenKind::Newline, sp) => {
                                        span.expand(sp);
                                    }
                                    (CatTokenKind::Symbol('"'), sp) => {
                                        span.expand(sp);
                                        s.push('"');
                                    }
                                    (CatTokenKind::Text, sp) => {
                                        span.expand(sp);
                                        s.push_str(&sp.extract());
                                    }
                                    _ => {
                                        return Err(DiagBuilder2::fatal(
                                            "Unknown escape sequence in string",
                                        )
                                        .span(span))
                                    }
                                }
                            }
                            (CatTokenKind::Newline, sp) => {
                                return Err(DiagBuilder2::fatal(
                                    "String literals cannot contain unescaped newlines",
                                )
                                .span(sp))
                            }
                            (_, sp) => {
                                span.expand(sp);
                                s.push_str(&sp.extract());
                            }
                        }
                        self.bump()?;
                    }
                    return Ok((Literal(Str(name_table.intern(&s, true))), span));
                }

                (CatTokenKind::Eof, sp) => return Ok((Eof, sp)),
                (tkn, sp) => {
                    return Err(DiagBuilder2::fatal(format!("Unknown token {:?}", tkn)).span(sp))
                }
            }
        }
    }

    /// Skips all input tokens that are excluded from the language's syntax,
    /// i.e. whitespace, newlines, and comments. Note that during lexical
    /// analysis whitespace may still play a vital role, espceially when parsing
    /// number literals or string constants.
    fn skip_noise(&mut self) -> DiagResult2<()> {
        loop {
            match (self.peek[0].0, self.peek[1].0) {
                // Single-line comment inserted by preprocessor.
                (CatTokenKind::Symbol('/'), CatTokenKind::Symbol('/')) => {
                    self.bump()?;
                    self.bump()?;
                    loop {
                        match self.peek[0].0 {
                            CatTokenKind::Eof => break,
                            CatTokenKind::Newline => {
                                self.bump()?;
                                break;
                            }
                            _ => self.bump()?,
                        }
                    }
                }
                // Multi-line comment inserted by preprocessor.
                (CatTokenKind::Symbol('/'), CatTokenKind::Symbol('*')) => {
                    self.bump()?;
                    self.bump()?;
                    loop {
                        match (self.peek[0].0, self.peek[1].0) {
                            (CatTokenKind::Eof, _) => break,
                            (CatTokenKind::Symbol('*'), CatTokenKind::Symbol('/')) => {
                                self.bump()?;
                                self.bump()?;
                                break;
                            }
                            _ => self.bump()?,
                        }
                    }
                }
                // SystemVerilog Attributes
                (CatTokenKind::Symbol('('), CatTokenKind::Symbol('*'))
                    if self.peek[2].0 != CatTokenKind::Symbol(')') =>
                {
                    self.bump()?;
                    self.bump()?;
                    loop {
                        match (self.peek[0].0, self.peek[1].0) {
                            (CatTokenKind::Eof, _) => break,
                            (CatTokenKind::Symbol('*'), CatTokenKind::Symbol(')')) => {
                                self.bump()?;
                                self.bump()?;
                                break;
                            }
                            _ => self.bump()?,
                        }
                    }
                }
                _ => (),
            }
            match self.peek[0].0 {
                CatTokenKind::Whitespace | CatTokenKind::Newline | CatTokenKind::Comment => {
                    self.bump()?
                }
                _ => return Ok(()),
            }
        }
    }

    /// Matches an identifier. This consumes all tokens from the input that when
    /// combined still make up a valid identifier and returns the consumed
    /// characters as a String, alongside the span they covered. In
    /// SystemVerilog upper- and lowercase characters, digits, underscores '_',
    /// and dollar signs '$' are all valid within an identifier.
    fn match_ident(&mut self) -> DiagResult2<(String, Span)> {
        let mut s = String::new();
        let mut sp = self.peek[0].1;
        loop {
            match self.peek[0] {
                (CatTokenKind::Text, this_sp)
                | (CatTokenKind::Digits, this_sp)
                | (CatTokenKind::Symbol('_'), this_sp)
                | (CatTokenKind::Symbol('$'), this_sp) => {
                    s.push_str(&this_sp.extract());
                    sp.expand(this_sp);
                    self.bump()?;
                }
                _ => break,
            }
        }
        if s.is_empty() {
            return Err(DiagBuilder2::fatal("Could not match an identifier here").span(sp));
        }
        assert!(!s.is_empty());
        Ok((s, sp))
    }

    /// This function assumes that we have just consumed the apostrophe `'`
    /// before the base indication.
    fn match_based_number(
        &mut self,
        size: Option<Name>,
        mut span: Span,
    ) -> DiagResult2<TokenAndSpan> {
        match self.peek[0] {
            (CatTokenKind::Text, sp) => {
                self.bump()?;
                let text = sp.extract();
                span.expand(sp);
                let mut chars = text.chars();
                let mut c = chars.next();

                // Consume the optional sign indicator or emit an unbased and
                // unsized literal if the apostrophe is immediately followed by
                // [zZxX].
                let signed = match c {
                    Some('s') | Some('S') => {
                        c = chars.next();
                        true
                    }
                    Some('z') | Some('Z') if text.len() == 1 => {
                        return Ok((Literal(UnbasedUnsized('z')), span))
                    }
                    Some('x') | Some('X') if text.len() == 1 => {
                        return Ok((Literal(UnbasedUnsized('x')), span))
                    }
                    _ => false,
                };

                // Consume the base of the number.
                let base = match c {
                    Some('d') | Some('D') => 'd',
                    Some('b') | Some('B') => 'b',
                    Some('o') | Some('O') => 'o',
                    Some('h') | Some('H') => 'h',
                    Some(x) => {
                        return Err(DiagBuilder2::fatal(format!(
                            "`{}` is not a valid number base",
                            x
                        ))
                        .span(span))
                    }
                    None => return Err(DiagBuilder2::fatal("Missing number base").span(span)),
                };
                c = chars.next();

                // If no more characters remain, a whitespace and subsequent
                // digits may follow. Otherwise, the remaining characters are to
                // be treated as part of the number body and no whitespace
                // follows.
                let mut body = String::new();
                if let Some(c) = c {
                    body.push(c);
                    body.push_str(chars.as_str());
                } else {
                    self.skip_noise()?;
                }
                self.eat_number_body_into(&mut body, &mut span, true)?;

                return Ok((
                    Literal(BasedInteger(
                        size,
                        signed,
                        base,
                        get_name_table().intern(&body, true),
                    )),
                    span,
                ));
            }

            (CatTokenKind::Digits, sp) if size.is_none() => {
                self.bump()?;
                let value = sp.extract();
                span.expand(sp);
                match value.chars().next() {
                    Some('0') if value.len() == 1 => {
                        return Ok((Literal(UnbasedUnsized('0')), span))
                    }
                    Some('1') if value.len() == 1 => {
                        return Ok((Literal(UnbasedUnsized('1')), span))
                    }
                    _ => {
                        return Err(DiagBuilder2::fatal(
                            "Unbased unsized literal may only be '0, '1, 'x, or 'z",
                        )
                        .span(span))
                    }
                }
            }

            (CatTokenKind::Symbol('?'), sp) => {
                self.bump()?;
                span.expand(sp);
                return Ok((Literal(UnbasedUnsized('z')), span));
            }

            // (_, sp) => return Err(DiagBuilder2::fatal("Invalid number base").span(sp))
            _ => return Ok((Apostrophe, span)),
        }
    }

    /// Eats all text, digits, and underscore tokens, accumulating them (except
    /// for the underscores) in a String.
    fn eat_number_body_into(
        &mut self,
        into: &mut String,
        span: &mut Span,
        allow_alphabetic: bool,
    ) -> DiagResult2<()> {
        loop {
            match self.peek[0] {
                (CatTokenKind::Digits, sp) | (CatTokenKind::Text, sp) => {
                    if self.peek[0].0 == CatTokenKind::Text && !allow_alphabetic {
                        break;
                    }
                    into.push_str(&sp.extract());
                    span.expand(sp);
                }
                (CatTokenKind::Symbol('_'), _) => (),
                (CatTokenKind::Symbol('?'), sp) => {
                    into.push('?');
                    span.expand(sp);
                }
                _ => break,
            }
            self.bump()?;
        }
        Ok(())
    }

    /// Try to parse the next text token as a time unit.
    fn try_time_unit(&mut self) -> Option<TimeUnit> {
        if self.peek[0].0 == CatTokenKind::Text {
            match self.peek[0].1.extract().as_str() {
                "s" => Some(TimeUnit::Second),
                "ms" => Some(TimeUnit::MilliSecond),
                "us" => Some(TimeUnit::MicroSecond),
                "ns" => Some(TimeUnit::NanoSecond),
                "ps" => Some(TimeUnit::PicoSecond),
                "fs" => Some(TimeUnit::FemtoSecond),
                _ => None,
            }
        } else {
            None
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = DiagResult2<TokenAndSpan>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.next_token() {
            Ok((Eof, _)) => None,
            x => Some(x),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(input: &str, expected: &[Token]) {
        use std::cell::Cell;
        thread_local!(static INDEX: Cell<usize> = Cell::new(0));
        let sm = get_source_manager();
        let idx = INDEX.with(|i| {
            let v = i.get();
            i.set(v + 1);
            v
        });
        let source = sm.add(&format!("test_{}.sv", idx), input);
        let pp = Preprocessor::new(source, &[], &[]);
        let lexer = Lexer::new(pp);
        let actual: Vec<_> = lexer.map(|x| x.unwrap().0).collect();
        assert_eq!(actual, expected);
    }

    fn check_single(input: &str, expected: Token) {
        check(input, &[expected]);
    }

    fn name(n: &str) -> Name {
        get_name_table().intern(n, true)
    }

    /// According to IEEE 1800-2009 5.6
    #[test]
    fn idents() {
        check(
            "shiftreg_a busa_index error_condition merge_ab _bus3 n$657",
            &vec![
                Ident(name("shiftreg_a")),
                Ident(name("busa_index")),
                Ident(name("error_condition")),
                Ident(name("merge_ab")),
                Ident(name("_bus3")),
                Ident(name("n$657")),
            ],
        );
    }

    /// According to IEEE 1800-2009 5.6.1
    #[test]
    fn esc_idents() {
        check(
            "\\busa+index \\-clock \\***error-condition*** \\net1/\\net2 \\{a,b} \\a*(b+c)",
            &vec![
                EscIdent(name("busa+index")),
                EscIdent(name("-clock")),
                EscIdent(name("***error-condition***")),
                EscIdent(name("net1/\\net2")),
                EscIdent(name("{a,b}")),
                EscIdent(name("a*(b+c)")),
            ],
        );
    }

    /// According to IEEE 1800-2009 5.6.3
    #[test]
    fn sys_idents() {
        check(
            "$display $finish $01_ad$as3_",
            &vec![
                SysIdent(name("display")),
                SysIdent(name("finish")),
                SysIdent(name("01_ad$as3_")),
            ],
        );
    }

    /// According to IEEE 1800-2009 5.7.1
    #[test]
    fn unbased_unsized_literal() {
        check_single("'0", Literal(UnbasedUnsized('0')));
        check_single("'1", Literal(UnbasedUnsized('1')));
        check_single("'X", Literal(UnbasedUnsized('x')));
        check_single("'x", Literal(UnbasedUnsized('x')));
        check_single("'Z", Literal(UnbasedUnsized('z')));
        check_single("'z", Literal(UnbasedUnsized('z')));
        check_single("'?", Literal(UnbasedUnsized('z')));
    }

    #[test]
    fn unsized_literal_constant_numbers() {
        check(
            "659; 'h 837FF; 'o7460",
            &[
                Literal(Number(name("659"), None)),
                Semicolon,
                Literal(BasedInteger(None, false, 'h', name("837FF"))),
                Semicolon,
                Literal(BasedInteger(None, false, 'o', name("7460"))),
            ],
        );
    }

    #[test]
    #[should_panic(expected = "number literal `4` may not directly be followed by letters `af`")]
    fn unsized_literal_constant_numbers_illegal() {
        check("4af", &vec![]);
    }

    #[test]
    fn sized_literal_constant_numbers() {
        check(
            "4'b1001; 5 'D 3; 3'b01x; 12'hx; 16'hz",
            &[
                Literal(BasedInteger(Some(name("4")), false, 'b', name("1001"))),
                Semicolon,
                Literal(BasedInteger(Some(name("5")), false, 'd', name("3"))),
                Semicolon,
                Literal(BasedInteger(Some(name("3")), false, 'b', name("01x"))),
                Semicolon,
                Literal(BasedInteger(Some(name("12")), false, 'h', name("x"))),
                Semicolon,
                Literal(BasedInteger(Some(name("16")), false, 'h', name("z"))),
            ],
        );
    }

    #[test]
    fn signed_literal_constant_numbers() {
        check(
            "4 'shf; 16'sd?",
            &[
                Literal(BasedInteger(Some(name("4")), true, 'h', name("f"))),
                Semicolon,
                Literal(BasedInteger(Some(name("16")), true, 'd', name("?"))),
            ],
        );
    }

    #[test]
    #[ignore]
    fn underscores_in_literal_constant_numbers() {
        check(
            "27_195_000; 16'b0011_0101_0001_1111; 32 'h 12ab_f001",
            &[
                Literal(Number(name("27195000"), None)),
                Semicolon,
                Literal(BasedInteger(
                    Some(name("16")),
                    false,
                    'b',
                    name("0011010100011111"),
                )),
                Semicolon,
                Literal(BasedInteger(Some(name("32")), false, 'h', name("12abf001"))),
            ],
        );
    }

    /// According to IEEE 1800-2009 5.9
    #[test]
    fn multiline_string_literal() {
        check(
            "$display(\"Humpty Dumpty sat on a wall. \\\nHumpty Dumpty had a great fall.\")",
            &[
                SysIdent(name("display")),
                OpenDelim(Paren),
                Literal(Str(name(
                    "Humpty Dumpty sat on a wall. Humpty Dumpty had a great fall.",
                ))),
                CloseDelim(Paren),
            ],
        );
    }

    #[test]
    fn time_literal() {
        check(
            "42s 14.3ms 16.32us 9ns 0.1ps 8123fs",
            &[
                Literal(Time(name("42"), None, TimeUnit::Second)),
                Literal(Time(name("14"), Some(name("3")), TimeUnit::MilliSecond)),
                Literal(Time(name("16"), Some(name("32")), TimeUnit::MicroSecond)),
                Literal(Time(name("9"), None, TimeUnit::NanoSecond)),
                Literal(Time(name("0"), Some(name("1")), TimeUnit::PicoSecond)),
                Literal(Time(name("8123"), None, TimeUnit::FemtoSecond)),
            ],
        );
    }

    #[test]
    fn number_literal() {
        check(
            "42 4.2",
            &[
                Literal(Number(name("42"), None)),
                Literal(Number(name("4"), Some(name("2")))),
            ],
        );
    }
}
