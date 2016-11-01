
use std::fmt;

use ::{ ParseResult, PResult, Parsed, Input, State };

/// Value for a failed end-of-input parse.
#[derive( Debug, Copy, Clone, PartialEq, Eq )]
pub struct NotEnd {
    /// The length of the rest of the input.
    pub left: usize,
}

impl fmt::Display for NotEnd {

    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "Expected end, found {} more bytes", self.left)
    }
}

/// Produces a parser matching only at the end of the input.
///
/// Returns a `()` value on a successful parse. When parsing failed, the `NotEnd` result
/// value will communicate the length of the rest of the input slice.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::end_of_input();
///
/// assert_eq!(
///     ab::get("", &parser),
///     Ok((
///         (),
///         ab::State::Incomplete,
///         "",
///     ))
/// );
///
/// assert_eq!(
///     ab::get("foo", &parser),
///     Err(ab::GetError::Failed(
///         ab::NotEnd { left: 3 },
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
pub fn end_of_input() -> impl Fn(Input) -> PResult<(), NotEnd, !> {
    |input| {
        if !input.is_empty() {
            Ok(ParseResult::new_failed(NotEnd { left: input.len() }, State::Complete, input))
        }
        else {
            Ok(ParseResult::new_parsed((), State::Incomplete, input))
        }
    }
}

/// Value for a failed end-of-line parse.
#[derive( Debug, Copy, Clone, PartialEq, Eq )]
pub struct NotLineEnd;

impl fmt::Display for NotLineEnd {

    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "Expected end of line")
    }
}

/// Produces a parser only matching at the end of input or by consuming a newline.
///
/// A successful parse result holds an `Option<char>` value that can be used to determine
/// if the match succeeded because of a consumed newline (which will be in the `Option`) or
/// because the end of input was reached.
///
/// Only a ASCII newline char (`'\n'`) will be considered a newline by this function.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::end_of_line();
///
/// assert_eq!(
///     ab::get("", &parser),
///     Ok((
///         None,
///         ab::State::Incomplete,
///         "",
///     ))
/// );
///
/// assert_eq!(
///     ab::get("\n", &parser),
///     Ok((
///         Some('\n'),
///         ab::State::Complete,
///         "",
///     ))
/// );
///
/// assert_eq!(
///     ab::get("foo", &parser),
///     Err(ab::GetError::Failed(
///         ab::NotLineEnd,
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
pub fn end_of_line<'a>() -> impl Fn(Input<'a>) -> PResult<Option<char>, NotLineEnd, !> {
    ::any(
        ::failed_map(::parsed_map(end_of_input(), |_, _| None), |_| NotLineEnd),
        ::failed_map(::parsed_map(::char_newline(), |s, _| Some(s)), |_| NotLineEnd),
    )
}

/// Value for a failed digit parse.
///
/// The `radix` field will contain the radix used when parsing was attempted.
#[derive( Debug, Copy, Clone, PartialEq, Eq )]
pub struct NoDigit { 
    /// The radix the digit was expected in.
    pub radix: u32,
}

impl fmt::Display for NoDigit {

    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "Expected a radix {} digit", self.radix)
    }
}

/// Produces a parser matching a digit of the specified radix.
///
/// A successful match will result in a `char` value. A failure will result in a
/// `NoDigit` value holding the passed radix.
///
/// # Errors
///
/// Returns an `InvalidRadix` error if the passed in radix is larger than 36.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// // parse hexadecimal digits
/// let parser = ab::char_digit(16).unwrap();
///
/// assert_eq!(
///     ab::get("c", &parser),
///     Ok((
///         'c',
///         ab::State::Complete,
///         "",
///     ))
/// );
///
/// assert_eq!(
///     ab::get("x", &parser),
///     Err(ab::GetError::Failed(
///         ab::NoDigit { radix: 16 },
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
pub fn char_digit<'a>(radix: u32)
-> Result<impl Fn(Input<'a>) -> PResult<'a, char, NoDigit, !>, InvalidRadix> {
    if radix > 36 {
        return Err(InvalidRadix);
    }
    Ok(move |input: Input<'a>| match input.slice().chars().nth(0) {
        Some(c) if c.is_digit(radix) => {
            let (_, rest) = input.consume(c.len_utf8());
            Ok(ParseResult::new_parsed(c, State::Complete, rest))
        },
        Some(_) => Ok(ParseResult::new_failed(NoDigit { radix: radix }, State::Complete, input)),
        None => Ok(ParseResult::new_failed(NoDigit { radix: radix }, State::Incomplete, input)),
    })
}

/// Error value for an invalid radix.
#[derive( Debug, Copy, Clone, PartialEq, Eq )]
pub struct InvalidRadix;

/// Value for a failed character parse.
#[derive( Debug, Copy, Clone, PartialEq, Eq )]
pub struct NoChar;

/// Produces a parser matching any `char`.
///
/// Will always succeed unless we've reached the end of input.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::char_any();
///
/// assert_eq!(
///     ab::get("foo", &parser),
///     Ok((
///         'f',
///         ab::State::Complete,
///         "oo",
///     ))
/// );
/// ```
#[inline]
pub fn char_any() -> impl Fn(Input) -> PResult<char, NoChar, !> {
    |input| match input.slice().chars().nth(0) {
        Some(c) => {
            let (_, rest) = input.consume(c.len_utf8());
            Ok(ParseResult::new_parsed(c, State::Complete, rest))
        },
        None => Ok(ParseResult::new_failed(NoChar, State::Incomplete, input)),
    }
}

/// Produces a parser capturing a `&str` slice until a sub-parser succeeds.
///
/// On success, the resulting value will be a `&str` up to but excluding the content
/// matched by the `end` sub-parser. The input covered by the `end` marker will be consumed
/// as well.
///
/// An error returned by the `end` sub-parser will cause iteration to cease and the error to
/// be returned immediately.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::str_until(ab::char_newline());
///
/// assert_eq!(
///     ab::get("some content\nnext line", &parser),
///     Ok((
///         "some content",
///         ab::State::Complete,
///         "next line",
///     ))
/// );
/// ```
pub fn str_until<'a, Y, N, E, F>(end: F)
-> impl Fn(Input<'a>)
-> PResult<&'a str, N, E>
where F: Fn(Input<'a>) -> PResult<Y, N, E> {
    move |input| {
        let mut current = input;
        let mut consumed = 0;
        loop {
            match end(current) {
                Ok(ParseResult::Parsed(Parsed { rest, state, .. })) => {
                    let (span, input_rest) = input.consume(consumed);
                    return Ok(ParseResult::new_parsed(
                        span,
                        input_rest.rest_state().merge(state),
                        rest,
                    ));
                },
                Ok(ParseResult::Failed(failed)) => match current.slice().chars().nth(0) {
                    Some(c) => {
                        let (_, new) = current.consume(c.len_utf8());
                        current = new;
                        consumed += c.len_utf8();
                    },
                    None => return Ok(ParseResult::Failed(failed)),
                },
                Err(error) => return Err(error),
            }
        }
    }
}

/// Produces a parser returning the `&str` covered by a sub-parser.
///
/// Errors and failures from the sub-parser will be passed through as is.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::str_capture(
///     ab::list(
///         ab::char_newline(),
///         ab::str_identifier(),
///         ab::ListLimit::Limited(1024),
///     ),
/// );
///
/// assert_eq!(
///     ab::get("foo\nbar\nbaz", &parser),
///     Ok((
///         "foo\nbar\nbaz",
///         ab::State::Incomplete,
///         "",
///     ))
/// );
/// ```
pub fn str_capture<'a, Y, N, E, F>(parser: F) -> impl Fn(Input<'a>) -> PResult<&'a str, N, E>
where F: Fn(Input<'a>) -> PResult<Y, N, E> {
    move |input| {
        let Parsed { rest, state, .. } = try_parsed!(parser(input));
        let len = rest.location().position - input.location().position;
        let (captured, rest) = input.consume(len);
        Ok(ParseResult::new_parsed(captured, state, rest))
    }
}

#[cfg(test)]
mod tests {

    #[test]
    fn char_digit() {
        test!(super::char_digit(16).unwrap(),
            "0" => (ok: '0', ""),
            "9" => (ok: '9', ""),
            "f" => (ok: 'f', ""),
            "F" => (ok: 'F', ""),
            "g" => (err: super::NoDigit { radix: 16 }, (0, 1, 1)),
            "G" => (err: super::NoDigit { radix: 16 }, (0, 1, 1)),
            "" => (err?: super::NoDigit { radix: 16 }, (0, 1, 1)),
        );
    }

    #[test]
    fn str_capture() {
        let limit = ::ListLimit::Unlimited;
        test!(super::str_capture(::list(::str_whitespace(), ::str_identifier(), limit)),
            "a b c" => (ok?: "a b c", ""),
            "a b c " => (ok?: "a b c", " "),
        );
    }

    #[test]
    fn str_until() {
        test!(super::str_until(::char_newline()),
            "foo\nbar\nbaz" => (ok: "foo", "bar\nbaz"),
            "foo\n " => (ok: "foo", " "),
            "f\n " => (ok: "f", " "),
            "\n " => (ok: "", " "),
            "" => (err?: ::NotExactChar { expected: '\n' }, (0, 1, 1)),
            "foo" => (err?: ::NotExactChar { expected: '\n' }, (3, 1, 4)),
        );
        test!(super::str_until(::str_identifier()),
            "  foo" => (ok?: "  ", ""),
            "  foo " => (ok: "  ", " "),
            "  " => (err?: ::NoIdentifier, (2, 1, 3)),
        );
    }

    #[test]
    fn char_any() {
        test!(super::char_any(),
            "foo" => (ok: 'f', "oo"),
            "f" => (ok: 'f', ""),
            "\t" => (ok: '\t', ""),
            "" => (err?: super::NoChar, (0, 1, 1)),
        );
    }

    #[test]
    fn end_of_line() {
        test!(super::end_of_line(),
            "" => (ok?: None, ""),
            "\n" => (ok: Some('\n'), ""),
            "\n " => (ok: Some('\n'), " "),
            " " => (err: super::NotLineEnd, (0, 1, 1)),
        );
    }

    #[test]
    fn end_of_input() {
        test!(super::end_of_input(),
            "" => (ok?: (), ""),
            " " => (err: super::NotEnd { left: 1 }, (0, 1, 1)),
            "\nab" => (err: super::NotEnd { left: 3 }, (0, 1, 1)),
        );
    }
}
