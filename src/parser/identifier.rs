
use std::fmt;

use ::{ PResult, ParseResult, State, Input };
    
fn is_identifier_start(c: char) -> bool {
    match c { 'a'...'z' | 'A'...'Z' | '_' => true, _ => false }
}

fn is_identifier_tail(c: char) -> bool {
    match c { 'a'...'z' | 'A'...'Z' | '0'...'9' | '_' => true, _ => false }
}

fn is_identifier(s: &str) -> bool {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if is_identifier_start(c) => (),
        _ => return false,
    }
    for c in chars {
        if !is_identifier_tail(c) {
            return false;
        }
    }
    true
}

/// Value for a failed identifier parse.
#[derive( Debug, Copy, Clone, PartialEq, Eq )]
pub struct NoIdentifier;

impl fmt::Display for NoIdentifier {

    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "Expected any identifier")
    }
}

/// Produces a parser matching any identifier.
///
/// An identifier begins with a letter or underscore, and continues with letters,
/// underscores, or digits.
///
/// The success result value is the `&str` holding the parsed identifier.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::str_identifier();
///
/// assert_eq!(
///     ab::get("foo_23", &parser),
///     Ok((
///         "foo_23",
///         ab::State::Incomplete,
///         "",
///     ))
/// );
/// ```
#[inline]
pub fn str_identifier() -> impl Fn(Input) -> PResult<&str, NoIdentifier, !> {
    |input| {
        let (value, rest) = match input.slice().chars().nth(0) {
            Some(c) if is_identifier_start(c) =>
                input.slice()
                    .char_indices()
                    .find(|&(_, c)| !is_identifier_tail(c))
                    .map_or_else(
                        || input.consume_all(),
                        |(p, _)| input.consume(p),
                    ),
            _ => return Ok(ParseResult::new_failed(NoIdentifier, input.rest_state(), input)),
        };
        Ok(ParseResult::new_parsed(value, rest.rest_state(), rest))
    }
}

/// Value for a failed keyword parse.
#[derive( Debug, Copy, Clone, PartialEq, Eq )]
pub enum KeywordError<'i, 'p> {
    /// An identifier was parsed, but it was a different one.
    WrongIdentifier {
        /// The expected keyword.
        expected: &'p str,
        /// The keyword that was found.
        found: &'i str,
    },
    /// No identifier could be parsed.
    NoIdentifier {
        /// The expected keyword.
        expected: &'p str,
    },
}

impl<'i, 'p> KeywordError<'i, 'p> {

    /// Create a `KeywordError::WrongIdentifier` value with the specified expected keyword.
    pub fn new_wrong(expected: &'p str, found: &'i str) -> Self {
        KeywordError::WrongIdentifier { expected: expected, found: found }
    }

    /// Create a `KeywordError::NoIdentifier` value with the specified expected keyword.
    pub fn new_none(expected: &'p str) -> Self {
        KeywordError::NoIdentifier { expected: expected }
    }
}

impl<'i, 'p> fmt::Display for KeywordError<'i, 'p> {

    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            KeywordError::WrongIdentifier { expected, found } =>
                write!(out, "Expected identifier '{}', found '{}'", expected, found),
            KeywordError::NoIdentifier { expected } =>
                write!(out, "Expected identifier '{}', found none", expected),
        }
    }
}

/// Produces a parser for a specific identifier.
///
/// The returned parser is built on `identifier`. As such, it will scan a full identifier
/// and then do a comparison.
///
/// A successful value is represented by a `&str` holding the identifier. A failed result
/// uses `KeywordError` to indicate the kind of failure.
///
/// # Error
///
/// Returns an `InvalidKeyword` error if the passed in keyword is not a valid identifier.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::str_keyword("foo").unwrap();
///
/// assert_eq!(
///     ab::get("foo", &parser),
///     Ok((
///         "foo",
///         ab::State::Incomplete,
///         "",
///     ))
/// );
///
/// assert_eq!(
///     ab::get("foobar", &parser),
///     Err(ab::GetError::Failed(
///         ab::KeywordError::WrongIdentifier {
///             expected: "foo",
///             found: "foobar",
///         },
///         ab::State::Complete,
///         ab::Location {
///             line: 1,
///             column: 1,
///             position: 0,
///         },
///     ))
/// );
/// ```
#[inline]
pub fn str_keyword<'p, 'i>(expected: &'p str)
-> Result<impl Fn(Input<'i>) -> PResult<'i, &'i str, KeywordError<'i, 'p>, !>, InvalidKeyword> {
    if !is_identifier(expected) {
        return Err(InvalidKeyword);
    }
    Ok(move |input| {
        str_identifier()(input).map(|result| match result {
            ParseResult::Parsed(::Parsed { value, state, rest }) if &value == &expected =>
                ParseResult::new_parsed(value, state, rest),
            ParseResult::Parsed(parsed) =>
                ParseResult::new_failed(
                    KeywordError::new_wrong(expected, parsed.value),
                    State::from_expected_input(input, expected),
                    input,
                ),
            ParseResult::Failed(failed) =>
                ParseResult::new_failed(
                    KeywordError::new_none(expected),
                    State::from_expected_input(input, expected).merge(failed.state),
                    input,
                ),
        })
    })
}

/// Error value for an invalid keyword specification.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct InvalidKeyword;

impl fmt::Display for InvalidKeyword {

    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "Invalid keyword")
    }
}

#[cfg(test)]
mod tests {

    #[test]
    fn str_identifier() {
        test!(super::str_identifier(),
            "f" => (ok?: "f", ""),
            "foo" => (ok?: "foo", ""),
            "foo_barBAZ23" => (ok?: "foo_barBAZ23", ""),
            "f " => (ok: "f", " "),
            "_ " => (ok: "_", " "),
            "foo " => (ok: "foo", " "),
            "_foo " => (ok: "_foo", " "),
            "" => (err?: super::NoIdentifier, (0, 1, 1)),
            "23" => (err: super::NoIdentifier, (0, 1, 1)),
            " foo" => (err: super::NoIdentifier, (0, 1, 1)),
        );
    }

    #[test]
    fn str_keyword() {
        macro_rules! wrong { ($e:expr) => {
            super::KeywordError::WrongIdentifier { expected: "foo_bar", found: $e };
        } }
        let none = super::KeywordError::NoIdentifier { expected: "foo_bar" };
        test!(super::str_keyword("foo_bar").unwrap(),
            "foo_bar" => (ok?: "foo_bar", ""),
            "foo_bar " => (ok: "foo_bar", " "),
            "foo_bar_baz" => (err: wrong!("foo_bar_baz"), (0, 1, 1)),
            "foo" => (err?: wrong!("foo"), (0, 1, 1)),
            "bar" => (err: wrong!("bar"), (0, 1, 1)),
            "" => (err?: none, (0, 1, 1)),
        );
    }
}
