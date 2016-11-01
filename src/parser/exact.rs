
use std::fmt;

use ::{ PResult, ParseResult, State, Input };

/// Value for a failed parse of an exact `&str'.
#[derive( Debug, Copy, Clone, PartialEq, Eq )]
pub struct NotExactStr<'p> {
    /// The expected `&str`.
    pub expected: &'p str,
}

impl<'p> fmt::Display for NotExactStr<'p> {

    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "Expected {:?}", self.expected)
    }
}

/// Produces a parser matching an exact `&str`.
///
/// This parser producer takes an expected `&str` value. The value will be reflected in
/// the `NotExactStr` error value if parsing failed.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::str_exact("foo");
///
/// assert_eq!(
///     ab::get("foo", &parser),
///     Ok(("foo", ab::State::Complete, ""))
/// );
/// ```
#[inline]
pub fn str_exact<'p>(expected: &'p str)
-> impl for<'i> Fn(Input<'i>)
-> PResult<'i, &'i str, NotExactStr<'p>, !> {
    move |input| {
        if input.slice().starts_with(expected) {
            let (value, rest) = input.consume(expected.len());
            Ok(ParseResult::new_parsed(value, State::Complete, rest))
        }
        else {
            Ok(ParseResult::new_failed(
                NotExactStr { expected: expected },
                State::from_expected_input(input, expected),
                input,
            ))
        }
    }
}

/// Value for a failed parse of an exact `char`.
#[derive( Debug, Copy, Clone, PartialEq, Eq )]
pub struct NotExactChar {
    /// The expected `char`.
    pub expected: char,
}

impl fmt::Display for NotExactChar {

    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "Expected {:?}", self.expected)
    }
}

/// Produces a parser matching an exact `char`.
///
/// This parser producer takes an expected `char` value. The value will be reflected in
/// the `NotExactChar` error value if parsing failed.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::char_exact('x');
///
/// assert_eq!(
///     ab::get("x", &parser),
///     Ok(('x', ab::State::Complete, ""))
/// );
/// ```
#[inline]
pub fn char_exact(expected: char) -> impl Fn(Input) -> PResult<char, NotExactChar, !> {
    move |input| {
        match input.slice().chars().nth(0) {
            Some(c) if c == expected => {
                let (_, rest) = input.consume(c.len_utf8());
                Ok(ParseResult::new_parsed(c, State::Complete, rest))
            },
            _ => Ok(ParseResult::new_failed(
                NotExactChar { expected: expected },
                input.rest_state(),
                input,
            )),
        }
    }
}

/// Produces a parser matching exactly one `'\n'`.
///
/// This is a version of `char_exact` that is specialised for `'\n'` characters for
/// documentation purposes. It will return a `NotExactChar` failure value if parsing fails.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::char_newline();
///
/// assert_eq!(
///     ab::get("\n", &parser),
///     Ok(('\n', ab::State::Complete, ""))
/// );
/// ```
#[inline]
pub fn char_newline() -> impl Fn(Input) -> PResult<char, NotExactChar, !> {
    char_exact('\n')
}

#[cfg(test)]
mod tests {

    #[test]
    fn char_newline() {
        test!(super::char_newline(),
            "\n\n " => (ok: '\n', "\n "),
            "\n" => (ok: '\n', ""),
            "\t" => (err: super::NotExactChar { expected: '\n' }, (0, 1, 1)),
            "" => (err?: super::NotExactChar { expected: '\n' }, (0, 1, 1)),
        );
    }

    #[test]
    fn char_exact() {
        test!(super::char_exact('x'),
            "x" => (ok: 'x', ""),
            "xy" => (ok: 'x', "y"),
            "xx" => (ok: 'x', "x"),
            "y" => (err: super::NotExactChar { expected: 'x' }, (0, 1, 1)),
            "" => (err?: super::NotExactChar { expected: 'x' }, (0, 1, 1)),
        );
    }

    #[test]
    fn str_exact() {
        test!(super::str_exact("foo"),
            "foo" => (ok: "foo", ""),
            "foobar" => (ok: "foo", "bar"),
            "foo " => (ok: "foo", " "),
            "bar" => (err: super::NotExactStr { expected: "foo" }, (0, 1, 1)),
            "f" => (err?: super::NotExactStr { expected: "foo" }, (0, 1, 1)),
            "f " => (err: super::NotExactStr { expected: "foo" }, (0, 1, 1)),
            "" => (err?: super::NotExactStr { expected: "foo" }, (0, 1, 1)),
        );
    }

}
