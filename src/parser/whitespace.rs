
use std::fmt;

use ::{ ParseResult, PResult, Input };

/// Value for a failed whitespace parse.
#[derive( Debug, Copy, Clone, PartialEq, Eq )]
pub struct NoWhitespace;

impl fmt::Display for NoWhitespace {

    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "Expected any whitespace")
    }
}

fn is_whitespace(c: char) -> bool {
    match c { ' ' | '\t' | '\n' => true, _ => false }
}

/// Produces a parser for any whitespace.
///
/// This parser only considers the ASCII space, tab, and newline characters as whitespace.
///
/// The success result will be a `&str` value holding all parsed whitspace.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::str_whitespace();
///
/// assert_eq!(
///     ab::get("   \n\tfoo", &parser),
///     Ok((
///         "   \n\t",
///         ab::State::Complete,
///         "foo",
///     ))
/// );
/// ```
#[inline]
pub fn str_whitespace()
-> impl Fn(Input)
-> Result<ParseResult<&str, NoWhitespace>, !> {
    |input| {
        let pos = input.slice().char_indices()
            .find(|&(_, c)| !is_whitespace(c))
            .map_or_else(|| input.len(), |(p, _)| p);
        match pos {
            0 => Ok(ParseResult::new_failed(NoWhitespace, input.rest_state(), input)),
            p => {
                let (slice, rest) = input.consume(p);
                Ok(ParseResult::new_parsed(slice, rest.rest_state(), rest))
            },
        }
    }
}

/// Produces a parser removing all leading and trailing whitespace.
///
/// The returned parser will apply `str_trim_left` and `str_trim_right` to the passed
/// sub-parser.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::str_trim(ab::str_identifier());
///
/// assert_eq!(
///     ab::get("  foo  ", &parser),
///     Ok((
///         "foo",
///         ab::State::Incomplete,
///         "",
///     ))
/// );
/// ```
pub fn str_trim<'a, Y, N, E, F>(parser: F)
-> impl Fn(Input<'a>)
-> PResult<Y, N, E>
where F: Fn(Input<'a>) -> PResult<Y, N, E> {
    str_trim_left(str_trim_right(parser))
}

/// Produces a parser removing all leading whitespace.
///
/// The returned parser will skip over all optional whitespace, then apply the sub-parser.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::str_trim_left(ab::str_identifier());
///
/// assert_eq!(
///     ab::get("  foo  ", &parser),
///     Ok((
///         "foo",
///         ab::State::Complete,
///         "  ",
///     ))
/// );
/// ```
pub fn str_trim_left<'a, Y, N, E, F>(parser: F)
-> impl Fn(Input<'a>)
-> PResult<Y, N, E>
where F: Fn(Input<'a>) -> PResult<Y, N, E> {
    ::failed_map(
        ::take_right(::infer_void_error(::optional(str_whitespace())), parser),
        |e| match e {
            ::PairError::Left(_)
                => panic!("str_tim_right received an unexpected failure from optional()"),
            ::PairError::Right(err) => err,
        },
    )
}

/// Produces a parser removing all trailing whitespace.
///
/// The returned parser will apply the sub-parser, then consume and drop all additional
/// whitespace.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::str_trim_right(ab::str_identifier());
///
/// assert_eq!(
///     ab::get("foo  ", &parser),
///     Ok((
///         "foo",
///         ab::State::Incomplete,
///         "",
///     ))
/// );
/// ```
pub fn str_trim_right<'a, Y, N, E, F>(parser: F)
-> impl Fn(Input<'a>)
-> PResult<Y, N, E>
where F: Fn(Input<'a>) -> PResult<Y, N, E> {
    ::failed_map(
        ::take_left(parser, ::infer_void_error(::optional(str_whitespace()))),
        |error| match error {
            ::PairError::Left(e) => e,
            ::PairError::Right(_)
                => panic!("str_tim_right received an unexpected failure from optional()"),
        },
    )
}

#[cfg(test)]
mod tests {

    #[test]
    fn str_trim() {
        test!(super::str_trim(::str_identifier()),
            "" => (err?: ::NoIdentifier, (0, 1, 1)),
            "  " => (err?: ::NoIdentifier, (2, 1, 3)),
            "foo" => (ok?: "foo", ""),
            "  foo" => (ok?: "foo", ""),
            "foo  " => (ok?: "foo", ""),
            "  foo  " => (ok?: "foo", ""),
            "  foo  !" => (ok: "foo", "!"),
        );
    }

    #[test]
    fn str_trim_left() {
        test!(super::str_trim_left(::str_identifier()),
            "" => (err?: ::NoIdentifier, (0, 1, 1)),
            "  " => (err?: ::NoIdentifier, (2, 1, 3)),
            "foo" => (ok?: "foo", ""),
            "  foo" => (ok?: "foo", ""),
            "foo  " => (ok: "foo", "  "),
            "  foo  " => (ok: "foo", "  "),
            "  foo  !" => (ok: "foo", "  !"),
        );
    }

    #[test]
    fn str_trim_right() {
        test!(super::str_trim_right(::str_identifier()),
            "" => (err?: ::NoIdentifier, (0, 1, 1)),
            "  " => (err: ::NoIdentifier, (0, 1, 1)),
            "foo" => (ok?: "foo", ""),
            "  foo" => (err: ::NoIdentifier, (0, 1, 1)),
            "foo  " => (ok?: "foo", ""),
            "foo  !" => (ok: "foo", "!"),
            "  foo  " => (err: ::NoIdentifier, (0, 1, 1)),
        );
    }

    #[test]
    fn str_whitespace() {
        test!(super::str_whitespace(),
            " " => (ok?: " ", ""),
            "\t" => (ok?: "\t", ""),
            "\n" => (ok?: "\n", ""),
            "" => (err?: super::NoWhitespace, (0, 1, 1)),
            "foo" => (err: super::NoWhitespace, (0, 1, 1)),
            "  \n \n \t  foo " => (ok: "  \n \n \t  ", "foo "),
        );
    }
}

