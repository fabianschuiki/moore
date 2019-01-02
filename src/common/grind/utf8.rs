// Copyright (c) 2017 Fabian Schuiki

//! A UTF8 parser that keeps track of the index and size of the characters it
//! emits. This parser does not generate any errors, but rather replaces invalid
//! encoding in the input with the `U+FFFD REPLACEMENT CHARACTER`.

use crate::grind::Grinder;
use std;

pub struct Utf8<T: Grinder<Item = Option<u8>>> {
    inner: T,
    current: usize,
    peek: Option<u8>,
}

impl<T> Utf8<T>
where
    T: Grinder<Item = Option<u8>>,
{
    /// Create a new UTF8 parser.
    pub fn new(mut inner: T) -> Utf8<T> {
        let peek = inner.next();
        Utf8 {
            inner: inner,
            current: 0,
            peek: peek,
        }
    }

    /// Advance the input by one position.
    fn bump(&mut self) {
        self.peek = self.inner.next();
        self.current += 1;
    }
}

impl<T> Grinder for Utf8<T>
where
    T: Grinder<Item = Option<u8>>,
{
    type Item = Option<(usize, char, u8)>;
    type Error = T::Error;

    fn next(&mut self) -> Self::Item {
        let offset = self.current;
        let lead = match self.peek {
            Some(c) => c,
            None => return None,
        };
        self.bump();
        let indicator = (!lead).leading_zeros() as u8;
        match indicator {
            // ASCII
            0 => Some((offset, lead as char, 1)),

            // Continuation byte without preceeding leading byte
            1 => Some((offset, '�', 1)),

            // Multi-byte encoding
            2 | 3 | 4 => {
                let mut v = lead as u32 & (0xFF >> indicator);
                for i in 1..indicator {
                    match self.peek {
                        Some(c) if (c >> 6 == 2) => v = (v << 6) | (c as u32 & 0x3F),
                        _ => return Some((offset, '�', i)),
                    }
                    self.bump();
                }
                Some((offset, std::char::from_u32(v).unwrap_or('�'), indicator))
            }

            // Invalid number of leading ones.
            _ => Some((offset, '�', 1)),
        }
    }

    fn emit(&mut self, err: Self::Error) {
        self.inner.emit(err)
    }
}
