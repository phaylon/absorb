
use std::fmt;

use ::{ ParseResult, PResult, Parsed, Failed, Input, State };

/// Value for a failure in one of two paired up parsers.
#[derive( Debug, Copy, Clone, PartialEq, Eq )]
pub enum PairError<L, R> {
    /// The left parser failed.
    Left(L),
    /// The right parser failed.
    Right(R),
}

impl<L, R> fmt::Display for PairError<L, R>
where L: fmt::Display, R: fmt::Display {

    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            PairError::Left(ref error) => write!(out, "Left Error: {}", error),
            PairError::Right(ref error) => write!(out, "Right Error: {}", error),
        }
    }
}

/// Produces a parser combining two sub-parsers into one result value.
///
/// Takes two sub-parsers and one combination function. On a successful parse, the combinator
/// function receives both sub-parsers result values and must return a new result value.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::combine(
///     ab::char_any(),
///     ab::char_any(),
///     |a, b| (a, b),
/// );
///
/// assert_eq!(
///     ab::get("ab", &parser),
///     Ok((
///         ('a', 'b'),
///         ab::State::Complete,
///         "",
///     ))
/// );
/// ```
pub fn combine<'a, Y1, Y2, N1, N2, F1, F2, E, C, Y>(f1: F1, f2: F2, comb: C)
-> impl Fn(Input<'a>)
-> PResult<Y, PairError<N1, N2>, E>
    where
        F1: Fn(Input<'a>) -> PResult<Y1, N1, E>,
        F2: Fn(Input<'a>) -> PResult<Y2, N2, E>,
        C: Fn(Y1, Y2) -> Y {
    let f1 = ::failed_map(f1, |e| PairError::Left(e));
    let f2 = ::failed_map(f2, |e| PairError::Right(e));
    move |input| {
        let Parsed { state, value: v1, rest } =
            try_parsed!(f1(input));
        let Parsed { state, value: v2, rest } =
            try_parsed!(f2(rest).map(|res| res.merge_state(state)));
        Ok(ParseResult::new_parsed(comb(v1, v2), state, rest))
    }
}

/// Value for a failed delimited structure.
#[derive( Debug, Copy, Clone, PartialEq, Eq )]
pub enum DelimitedError<L, C, R> {
    /// The left sub-parser failed.
    Left(L),
    /// The center sub-parser failed.
    Center(C),
    /// The right sub-parser failed.
    Right(R),
}

impl<L, C, R> fmt::Display for DelimitedError<L, C, R>
where L: fmt::Display, C: fmt::Display, R: fmt::Display {

    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            DelimitedError::Left(ref error) => write!(out, "Left Delimiter Error: {}", error),
            DelimitedError::Center(ref error) => write!(out, "Center Item Error: {}", error),
            DelimitedError::Right(ref error) => write!(out, "Right Delimiter Error: {}", error),
        }
    }
}

/// Produces a parser for delimited structures.
///
/// Will attempt to parse the `left`, `center` and `right` sub-parsers in sequence, and
/// return the `center` success value if all could be parsed.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::delimited(
///     ab::char_exact('['),
///     ab::str_identifier(),
///     ab::char_exact(']'),
/// );
///
/// assert_eq!(
///     ab::get("[foo]", &parser),
///     Ok((
///         "foo",
///         ab::State::Complete,
///         "",
///     ))
/// );
/// ```
pub fn delimited<'a, L, LR, LE, R, RR, RE, I, IR, IE, E>(left: L, center: I, right: R)
-> impl Fn(Input<'a>)
-> PResult<IR, DelimitedError<LE, IE, RE>, E>
    where
        L: Fn(Input<'a>) -> PResult<LR, LE, E>,
        R: Fn(Input<'a>) -> PResult<RR, RE, E>,
        I: Fn(Input<'a>) -> PResult<IR, IE, E> {
    let left = ::failed_map(left, |e| DelimitedError::Left(e));
    let center = ::failed_map(center, |e| DelimitedError::Center(e));
    let right = ::failed_map(right, |e| DelimitedError::Right(e));
    move |input| {
        let Parsed { state, rest, .. } =
            try_parsed!(left(input));
        let Parsed { state, value, rest } =
            try_parsed!(center(rest).map(|res| res.merge_state(state)));
        let Parsed { state, rest, .. } =
            try_parsed!(right(rest).map(|res| res.merge_state(state)));
        Ok(ParseResult::new_parsed(value, state, rest))
    }
}

/// Produces a parser for optional sub-parsers.
///
/// Takes a sub-parser and returns a `Some(_)` result on a successful parse and a
/// `None` on a failed one. Errors are still treated as errors.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::optional(ab::str_identifier());
///
/// assert_eq!(
///     ab::get("foo", &parser),
///     Ok((
///         Some("foo"),
///         ab::State::Incomplete,
///         "",
///     ))
/// );
///
/// assert_eq!(
///     ab::get("23", &parser),
///     Ok((
///         None,
///         ab::State::Complete,
///         "23",
///     ))
/// );
/// ```
pub fn optional<'a, Y, N, E, F>(parser: F)
-> impl Fn(Input<'a>)
-> PResult<Option<Y>, !, E>
where F: Fn(Input<'a>) -> PResult<Y, N, E> {
    move |input| {
        parser(input).map(|result| match result {
            ParseResult::Parsed(Parsed { value, state, rest }) =>
                ParseResult::new_parsed(Some(value), state, rest),
            ParseResult::Failed(Failed { state, .. }) =>
                ParseResult::new_parsed(None, state, input),
        })
    }
}

/// Produces a parser returning the right-hand result.
///
/// Takes two sub-parsers. It will return the right result if both sub-parsers succeed.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::take_right(
///     ab::char_any(),
///     ab::char_any(),
/// );
///
/// assert_eq!(
///     ab::get("ab", &parser),
///     Ok((
///         'b',
///         ab::State::Complete,
///         "",
///     ))
/// );
/// ```
pub fn take_right<'a, E1, F1, R1, E2, F2, R2, E>(left: F1, right: F2)
-> impl Fn(Input<'a>)
-> PResult<R2, PairError<E1, E2>, E>
    where
        F1: Fn(Input<'a>) -> PResult<R1, E1, E>,
        F2: Fn(Input<'a>) -> PResult<R2, E2, E> {
    let left = ::failed_map(left, |e| PairError::Left(e));
    let right = ::failed_map(right, |e| PairError::Right(e));
    move |input| {
        let Parsed { state, rest, .. } = try_parsed!(left(input));
        right(rest).map(|result| result.merge_state(state))
    }
}

/// Produces a parser returning the left-hand result.
///
/// Takes two sub-parsers. It will return the left result if both sub-parsers succeed.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::take_left(
///     ab::char_any(),
///     ab::char_any(),
/// );
///
/// assert_eq!(
///     ab::get("ab", &parser),
///     Ok((
///         'a',
///         ab::State::Complete,
///         "",
///     ))
/// );
/// ```
pub fn take_left<'a, E1, F1, R1, E2, F2, R2, E>(left: F1, right: F2)
-> impl Fn(Input<'a>)
-> PResult<R1, PairError<E1, E2>, E>
    where
        F1: Fn(Input<'a>) -> PResult<R1, E1, E>,
        F2: Fn(Input<'a>) -> PResult<R2, E2, E> {
    let left = ::failed_map(left, |e| PairError::Left(e));
    let right = ::failed_map(right, |e| PairError::Right(e));
    move |input| {
        let Parsed { state, rest, value } =
            try_parsed!(left(input));
        let Parsed { rest, state, .. } =
            try_parsed!(right(rest).map(|result| result.merge_state(state)));
        Ok(ParseResult::new_parsed(value, state, rest))
    }
}

/// Produces a zero-length parser that always succeeds.
///
/// Always returns a successful `()` result without consuming any input.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::nothing();
///
/// assert_eq!(
///     ab::get("foo", &parser),
///     Ok((
///         (),
///         ab::State::Complete,
///         "foo",
///     ))
/// );
/// ```
#[inline]
pub fn nothing() -> impl Fn(Input) -> PResult<(), !, !> {
    |input| Ok(ParseResult::new_parsed((), State::Complete, input))
}

/// A value for a pair of parse failure values.
#[derive( Debug, Copy, Clone, PartialEq, Eq )]
pub struct Neither<E1, E2> {
    /// The first error, usually the left parser.
    pub first: E1,
    /// The second error, usually the right parser.
    pub second: E2,
}

impl<A, B> fmt::Display for Neither<A, B>
where A: fmt::Display, B: fmt::Display {

    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "None of the expected alternatives could be parsed")
    }
}

/// Produces a parser for alternative sub-parsers returning all failures.
///
/// Tries the left sub-parser first, and the second if the first fails. When both fail
/// a `Neither` with both failures is returned.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::either(
///     ab::char_exact('a'),
///     ab::char_exact('b'),
/// );
///
/// assert_eq!(
///     ab::get("a", &parser),
///     Ok((
///         'a',
///         ab::State::Complete,
///         "",
///     ))
/// );
///
/// assert_eq!(
///     ab::get("b", &parser),
///     Ok((
///         'b',
///         ab::State::Complete,
///         "",
///     ))
/// );
///
/// assert_eq!(
///     ab::get("c", &parser),
///     Err(ab::GetError::Failed(
///         ab::Neither {
///             first: ab::NotExactChar { expected: 'a' },
///             second: ab::NotExactChar { expected: 'b' },
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
pub fn either<'a, F1, E1, F2, E2, R, E>(f1: F1, f2: F2)
-> impl Fn(Input<'a>)
-> PResult<R, Neither<E1, E2>, E>
where F1: Fn(Input<'a>) -> PResult<R, E1, E>, F2: Fn(Input<'a>) -> PResult<R, E2, E> {
    move |input| {
        let Failed { error: error1, state, .. } =
            try_failed!(f1(input));
        let Failed { error: error2, state, .. } =
            try_failed!(f2(input).map(|result| result.merge_state(state)));
        Ok(ParseResult::new_failed(Neither { first: error1, second: error2 }, state, input))
    }
}

/// Produces a parser for alternative sub-parsers returning the last failure.
///
/// Tries the left sub-parser first, and the second if the first fails. When both fail
/// the second failure value is returned.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::any(
///     ab::char_exact('a'),
///     ab::char_exact('b'),
/// );
///
/// assert_eq!(
///     ab::get("a", &parser),
///     Ok((
///         'a',
///         ab::State::Complete,
///         "",
///     ))
/// );
///
/// assert_eq!(
///     ab::get("b", &parser),
///     Ok((
///         'b',
///         ab::State::Complete,
///         "",
///     ))
/// );
///
/// assert_eq!(
///     ab::get("c", &parser),
///     Err(ab::GetError::Failed(
///         ab::NotExactChar { expected: 'b' },
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
pub fn any<'a, E1, F1, E2, F2, R, E>(f1: F1, f2: F2)
-> impl Fn(Input<'a>)
-> PResult<R, E2, E>
where F1: Fn(Input<'a>) -> PResult<R, E1, E>, F2: Fn(Input<'a>) -> PResult<R, E2, E> {
    move |input| {
        let Failed { state, .. } = try_failed!(f1(input));
        f2(input).map(|result| result.merge_state(state))
    }
}

/// Produces a parser that performs a zero-length match of the passed sub-parser.
///
/// The sub-parser will be applied as usual, but after the call to `peek` parsing will
/// continue at the same position.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::peek(ab::str_identifier());
///
/// assert_eq!(
///     ab::get("foo bar", &parser),
///     Ok((
///         "foo",
///         ab::State::Complete,
///         "foo bar",
///     ))
/// );
/// ```
pub fn peek<'a, Y, N, F, E>(parser: F)
-> impl Fn(Input<'a>)
-> PResult<'a, Y, N, E>
where F: Fn(Input<'a>) -> PResult<'a, Y, N, E> {
    move |input| parser(input).map(|result| {
        match result {
            ParseResult::Parsed(Parsed { value, state, .. }) =>
                ParseResult::Parsed(Parsed { value: value, state: state, rest: input }),
            other => other,
        }
    })
}

#[cfg(test)]
mod tests {
        
    fn l<L, R>(v: L) -> super::PairError<L, R> { super::PairError::Left(v) }
    fn r<L, R>(v: R) -> super::PairError<L, R> { super::PairError::Right(v) }

    #[test]
    fn peek() {
        test!(super::peek(::str_identifier()),
            "foo" => (ok?: "foo", "foo"),
            "" => (err?: ::NoIdentifier, (0, 1, 1)),
            "23" => (err: ::NoIdentifier, (0, 1, 1)),
        );
    }

    #[test]
    fn any() {
        test!(
            super::any(
                super::any(
                    ::str_exact("foo"),
                    ::str_exact("bar"),
                ),
                ::infer_void_parsed(::fail(::State::Complete, 23)),
            ),
            "foo" => (ok: "foo", ""),
            "bar" => (ok: "bar", ""),
            "fo" => (err?: 23, (0, 1, 1)),
            "ba" => (err?: 23, (0, 1, 1)),
            "" => (err?: 23, (0, 1, 1)),
            "qux" => (err: 23, (0, 1, 1)),
        );
    }

    #[test]
    fn either() {
        let make_error = || super::Neither {
            first: ::NotExactStr { expected: "foo" },
            second: ::NotExactStr { expected: "bar" },
        };
        test!(super::either(::str_exact("foo"), ::str_exact("bar")),
            "foo" => (ok: "foo", ""),
            "foo " => (ok: "foo", " "),
            "foobar" => (ok: "foo", "bar"),
            "bar" => (ok: "bar", ""),
            "baz" => (err: make_error(), (0, 1, 1)),
            "f" => (err?: make_error(), (0, 1, 1)),
            "ba" => (err?: make_error(), (0, 1, 1)),
            "" => (err?: make_error(), (0, 1, 1)),
        );
        test!(super::either(::str_identifier(), ::str_exact("")),
            "foo" => (ok?: "foo", ""),
            "foo " => (ok: "foo", " "),
            "" => (ok?: "", ""),
        );
    }

    #[test]
    fn nothing() {
        test!(super::nothing(),
            "" => (ok: (), ""),
            " " => (ok: (), " "),
            "foo" => (ok: (), "foo"),
        );
    }

    #[test]
    fn take_right() {
        let err_left = l(::NotExactStr { expected: "foo" });
        let err_right = r(::NotExactStr { expected: "bar" });
        test!(super::take_right(::str_exact("foo"), ::str_exact("bar")),
            "foobar" => (ok: "bar", ""),
            "foobarbaz" => (ok: "bar", "baz"),
            "foob" => (err?: err_right, (3, 1, 4)),
            "foo" => (err?: err_right, (3, 1, 4)),
            "foobyr" => (err: err_right, (3, 1, 4)),
            "f" => (err?: err_left, (0, 1, 1)),
            "" => (err?: err_left, (0, 1, 1)),
            "fyybar" => (err: err_left, (0, 1, 1)),
        );
    }

    #[test]
    fn take_left() {
        let err_left = l(::NotExactStr { expected: "foo" });
        let err_right = r(::NotExactStr { expected: "bar" });
        test!(super::take_left(::str_exact("foo"), ::str_exact("bar")),
            "foobar" => (ok: "foo", ""),
            "foobarbaz" => (ok: "foo", "baz"),
            "foob" => (err?: err_right, (3, 1, 4)),
            "foo" => (err?: err_right, (3, 1, 4)),
            "foobyr" => (err: err_right, (3, 1, 4)),
            "f" => (err?: err_left, (0, 1, 1)),
            "" => (err?: err_left, (0, 1, 1)),
            "fyybar" => (err: err_left, (0, 1, 1)),
        );
    }

    #[test]
    fn optional() {
        test!(super::optional(::str_identifier()),
            "foo" => (ok?: Some("foo"), ""),
            "foo " => (ok: Some("foo"), " "),
            "" => (ok?: None, ""),
            " " => (ok: None, " "),
            "23 " => (ok: None, "23 "),
        );
    }

    #[test]
    fn delimited() {
        test!(
            super::delimited(
                ::str_identifier(),
                ::str_whitespace(),
                ::str_keyword("b").unwrap(),
            ),
            "a b" => (ok?: " ", ""),
            "a b " => (ok: " ", " "),
        );
        let err_left = super::DelimitedError::Left(::NotExactStr { expected: "(" });
        let err_right = super::DelimitedError::Right(::NotExactStr { expected: ")" });
        let err_center = super::DelimitedError::Center(::NoIdentifier);
        test!(super::delimited(::str_exact("("), ::str_identifier(), ::str_exact(")")),
            "(foo)" => (ok: "foo", ""),
            "(foo." => (err: err_right, (4, 1, 5)),
            "(foo )" => (err: err_right, (4, 1, 5)),
            "(foo" => (err?: err_right, (4, 1, 5)),
            "( foo" => (err: err_center, (1, 1, 2)),
            "(23" => (err: err_center, (1, 1, 2)),
            "(" => (err?: err_center, (1, 1, 2)),
            "()" => (err: err_center, (1, 1, 2)),
            "23" => (err: err_left, (0, 1, 1)),
            "" => (err?: err_left, (0, 1, 1)),
        );
    }

    #[test]
    fn combine() {
        test!(super::combine(::str_exact("foo"), ::str_exact("bar"), |a, b| (a, b)),
            "foobar" => (ok: ("foo", "bar"), ""),
            "foobarbaz" => (ok: ("foo", "bar"), "baz"),
            "fyybarbaz" => (err: l(::NotExactStr { expected: "foo" }), (0, 1, 1)),
            "foobyrbaz" => (err: r(::NotExactStr { expected: "bar" }), (3, 1, 4)),
            "foob" => (err?: r(::NotExactStr { expected: "bar" }), (3, 1, 4)),
            "foo" => (err?: r(::NotExactStr { expected: "bar" }), (3, 1, 4)),
            "f" => (err?: l(::NotExactStr { expected: "foo" }), (0, 1, 1)),
            "" => (err?: l(::NotExactStr { expected: "foo" }), (0, 1, 1)),
        );
    }
}
