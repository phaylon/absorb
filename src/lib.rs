#![feature( conservative_impl_trait, never_type )]
#![warn( missing_docs )]

//! An experimental parser combinator library based on `impl Fn(..) -> ..` types.
//!
//! # Description
//!
//! In the context of this library, a parser is anything implementing
//! `Fn(Input<'a>) -> PResult<'a, _, _, _>`.
//!
//! # Parsing Functions
//!
//! The `get`, `parse` and `document` functions can be used to apply parsers to input
//! `&str` values:
//!
//! * The `parse` function is the raw parser application function.
//! * The `get` function is a convenience function to parse from the beginning of a
//!   `&str`.
//! * The `document` function is a convenience function to parse a full document contained
//!   in a `&str`.

use std::fmt;

#[macro_use]
mod test_util;

#[macro_use]
mod macros;

mod result;
pub use result::*;

mod parser;
pub use parser::*;

/// Input consumption interface.
///
/// You cannot directly generate a value of this type. The main parsing functions take
/// a `&str` value and a parser, and will wrap the input in this interface before passing
/// it to the parser for consumption.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Input<'a> {
    slice: &'a str,
    location: Location,
}

impl<'a> Input<'a> {

    /// Access the leftover input as slice.
    #[inline]
    pub fn slice(&self) -> &'a str { self.slice }

    /// The length of the leftover input slice.
    #[inline]
    pub fn len(&self) -> usize { self.slice.len() }

    /// A predicate checking if the leftover input slice is empty.
    ///
    /// This indicates the end of input has been reached.
    #[inline]
    pub fn is_empty(&self) -> bool { self.slice.len() == 0 }

    /// Construct a `Location` for the current input position.
    #[inline]
    pub fn location(&self) -> Location { self.location }

    /// Consume all leftover input.
    #[inline]
    pub fn consume_all(&self) -> (&'a str, Input<'a>) {
        self.consume(self.len())
    }

    /// Returns a `State::Complete` if there is more input to parse.
    #[inline]
    pub fn rest_state(&self) -> State { State::from_rest(*self) }

    /// Consume a specific input length.
    pub fn consume(&self, len: usize) -> (&'a str, Input<'a>) {
        assert!(
            self.slice.len() >= len,
            "not enough input left to consume (has {} bytes, was asked for {}",
            self.slice.len(),
            len
        );
        let parsed = &self.slice[..len];
        let rest = &self.slice[len..];
        let line_add = parsed.chars().filter(|c| *c == '\n').count();
        let last_line = match parsed.char_indices().rev().find(|&(_, c)| c == '\n') {
            Some((p, c)) => &parsed[(p + c.len_utf8())..],
            None => parsed,
        };
        let column_add = last_line.chars().count();
        (parsed, Input {
            slice: rest,
            location: Location {
                position: self.location.position + len,
                line: self.location.line + line_add,
                column: self.location.column + column_add,
            }
        })
    }
}

/// A location during input consumption.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Location {
    /// The line number of this location in the input slice.
    ///
    /// Begins at 1.
    pub line: usize,
    /// The column number of this location in the input slice.
    ///
    /// Begins at 1 and counts from the beginning of the line.
    pub column: usize,
    /// The position of this location in the input slice.
    ///
    /// Begins at 0 and is suitable for further slicing of the input.
    pub position: usize,
}

impl<'a> From<Input<'a>> for Location {

    fn from(input: Input<'a>) -> Location { input.location() }
}

impl Default for Location {

    fn default() -> Location {
        Location {
            line: 1,
            column: 1,
            position: 0,
        }
    }
}

impl fmt::Display for Location {

    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "line {}, column {}", self.line, self.column)
    }
}

/// Completion state indicator.
///
/// A complete value indicates that the parsed value will not change with additional
/// input.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum State {
    /// No further input required.
    Complete,
    /// Further input required.
    Incomplete,
}

impl fmt::Display for State {

    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "{}", match *self {
            State::Complete => "complete",
            State::Incomplete => "incomplete",
        })
    }
}

impl State {

    /// Merge this state with another.
    ///
    /// If one of the states is `Incomplete`, the resulting state will also be
    /// `Incomplete`. Otherwise a `Complete` state is returned.
    #[inline]
    pub fn merge(self, other: State) -> State {
        match (self, other) {
            (State::Complete, State::Complete) => State::Complete,
            _ => State::Incomplete,
        }
    }

    #[inline]
    fn from_expected_input(input: Input, expected: &str) -> State {
        if input.len() >= expected.len() { State::Complete }
        else if expected.starts_with(input.slice()) { State::Incomplete }
        else { State::Complete }
    }

    #[inline]
    fn from_rest(input: Input) -> State {
        if !input.is_empty() { State::Complete }
        else { State::Incomplete }
    }
}

/// An error from the `get` parse function.
#[derive( Debug, Copy, Clone, PartialEq, Eq )]
pub enum GetError<F, E> {
    /// Parsing has failed with the given result and state at the
    /// provided location.
    Failed(F, State, Location),
    /// An error has occured.
    Error(E),
}

impl<F, E> fmt::Display for GetError<F, E>
where F: fmt::Display, E: fmt::Display {

    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            GetError::Failed(ref error, _, location) =>
                write!(out, "Parse Error at {}: {}", location, error),
            GetError::Error(ref error) =>
                error.fmt(out),
        }
    }
}

/// A utility function for parsing from the beginning of a `&str`.
pub fn get<'a, Y, N, E, P>(input_str: &'a str, parser: P)
-> Result<(Y, State, &'a str), GetError<N, E>>
where P: Fn(Input<'a>) -> PResult<'a, Y, N, E> {
    match parse(input_str, parser, None) {
        Ok(ParseResult::Parsed(Parsed { value, rest, state }))
            => Ok((value, state, rest.slice())),
        Ok(ParseResult::Failed(Failed { error, location, state }))
            => Err(GetError::Failed(error, state, location)),
        Err(error)
            => Err(GetError::Error(error)),
    }
}

/// The raw parsing function applying a parser to an input `&str`.
pub fn parse<'a, Y, N, E, P>(input_str: &'a str, parser: P, last: Option<Location>)
-> PResult<'a, Y, N, E>
where P: Fn(Input<'a>) -> PResult<'a, Y, N, E> {
    parser(Input {
        slice: input_str,
        location: last.unwrap_or(Location::default()),
    })
}

/// An error from the `document` parse function.
#[derive( Debug, Copy, Clone, PartialEq, Eq )]
pub enum DocumentError<PE, E> {
    /// Parsing has failed with the given error at the given location.
    Parse {
        /// The parse failure value.
        error: PE,
        /// The location at which the parse error occured.
        location: Location,
    },
    /// There is leftover input that couldn't be parsed.
    Unparsed {
        /// The location where the unparsed input begins.
        location: Location,
    },
    /// An error occured.
    Fatal {
        /// The fatal error returned from the parser.
        error: E,
    },
}

impl<F, E> fmt::Display for DocumentError<F, E>
where F: fmt::Display, E: fmt::Display {

    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            DocumentError::Parse { ref error, location } =>
                write!(out, "Parse Error at {}: {}", location, error),
            DocumentError::Unparsed { location } =>
                write!(out, "Unparsable input at {}", location),
            DocumentError::Fatal { ref error } =>
                error.fmt(out),
        }
    }
}

/// Utility function for parsing a whole document.
///
/// Ensures that the whole input `&str` has been parsed.
pub fn document<'a, Y, N, E, F>(input: &'a str, parser: F)
-> Result<Y, DocumentError<N, E>>
where F: Fn(Input<'a>) -> PResult<Y, N, E> {
    match parse(input, take_left(parser, infer_void_error(end_of_input())), None) {
        Ok(ParseResult::Parsed(Parsed { value, .. })) => Ok(value),
        Ok(ParseResult::Failed(Failed { error, location, .. })) => Err(match error {
            PairError::Left(p_error)
                => DocumentError::Parse { error: p_error, location: location },
            PairError::Right(_)
                => DocumentError::Unparsed { location: location },
        }),
        Err(error) => Err(DocumentError::Fatal { error: error }),
    }
}

#[cfg(test)]
mod tests {

    #[test]
    fn get() {
        assert_eq!(
            super::get("foo", super::str_identifier()),
            Ok((
                "foo",
                super::State::Incomplete,
                "",
            ))
        );
        assert_eq!(
            super::get("23", super::str_identifier()),
            Err(super::GetError::Failed(
                super::NoIdentifier,
                super::State::Complete,
                super::Location {
                    line: 1,
                    column: 1,
                    position: 0,
                },
            ))
        );
        assert_eq!(
            super::get("", super::error(23)),
            Err(super::GetError::Error(23))
        );
    }

    #[test]
    fn document_item() {
        let loc = |p, l, c| ::Location { position: p, line: l, column: c };
        let doc = |input| ::document(input, ::str_identifier());
        assert_eq!(doc("xxx"), Ok("xxx"));
        assert_eq!(doc("23"), Err(::DocumentError::Parse {
            error: ::NoIdentifier,
            location: loc(0, 1, 1),
        }));
    }

    #[test]
    fn document_list() {
        let loc = |p, l, c| ::Location { position: p, line: l, column: c };
        let limit = ::ListLimit::Limited(3);
        let doc = |input| ::document(input, ::list(::nothing(), ::char_exact('x'), limit));
        assert_eq!(doc("xxx"), Ok(vec!['x', 'x', 'x']));
        assert_eq!(doc("xxy"), Err(::DocumentError::Unparsed { location: loc(2, 1, 3) }));
        assert_eq!(doc("xxxx"), Err(::DocumentError::Fatal {
            error: ::ListError::LimitExceeded { limit: 3 },
        }));
    }
}
