// Copyright (c) 2016-2020 Fabian Schuiki

use moore_common::errors::*;
use moore_common::source::*;

/// A generalized stream of tokens that accepts emission of diagnostics and
/// tracking of the severity of issues encountered.
pub trait TokenStream<T> {
    /// Look ahead at a token in the stream.
    fn peek(&mut self, offset: usize) -> Spanned<T>;

    /// Consume the current token.
    fn bump(&mut self);

    /// Skip the current token. Usually the same as `bump`, but may be used to
    /// keep skipped tokens out of the consumed tokens count by some parsers.
    fn skip(&mut self) {
        self.bump()
    }

    /// Get the number of tokens consumed. Excludes tokens skipped with `skip`.
    fn consumed(&self) -> usize;

    /// Get the span of the last token consumed token (bumped or skipped).
    fn last_span(&self) -> Span;

    /// Get the tail location of the last consumed token (bumped or skipped).
    fn last_loc(&self) -> Location {
        self.last_span().end()
    }

    /// Emit a diagnostic.
    fn emit(&mut self, diag: DiagBuilder2);

    /// Get the severity of the worst diagnostic emitted so far.
    fn severity(&self) -> Severity;

    /// Check whether a fatal diagnostic has been emitted.
    fn is_fatal(&self) -> bool {
        self.severity() >= Severity::Fatal
    }

    /// Check whether an error diagnostic has been emitted.
    fn is_error(&self) -> bool {
        self.severity() >= Severity::Error
    }
}
