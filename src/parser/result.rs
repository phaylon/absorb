
use ::{ PResult, ParseResult, Parsed, Failed, Input, State };

/// Produces a zero-length parser that only succeeds when the sub-parser fails.
///
/// Produces a successful `()` value when the sub-parser fails, or returns the
/// result of the sub-parser as a failed result when it matches.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
/// let parser = ab::not(ab::str_whitespace());
///
/// assert_eq!(
///     ab::get("foo", &parser),
///     Ok(((), ab::State::Complete, "foo"))
/// );
///
/// assert_eq!(
///     ab::get("   ", &parser),
///     Err(ab::GetError::Failed(
///         "   ",
///         ab::State::Incomplete,
///         ab::Location { line: 1, column: 1, position: 0 },
///     ))
/// );
/// ```
pub fn not<'a, Y, N, E, F>(parser: F)
-> impl Fn(Input<'a>)
-> PResult<(), Y, E>
where F: Fn(Input<'a>) -> PResult<Y, N, E> {
    move |input| match parser(input) {
        Err(error) => Err(error),
        Ok(ParseResult::Parsed(parsed)) =>
            Ok(ParseResult::new_failed(parsed.value, parsed.state, input)),
        Ok(ParseResult::Failed(failed)) =>
            Ok(ParseResult::new_parsed((), failed.state, input)),
    }
}

/// Produces a pass-through helper parser for sub-parsers returning `!` errors.
///
/// This function takes a sub-parser returning a `!` error, but returns a parser with a generic
/// error type.  It can be used to counter type mismatch errors when parsers with `!` errors are
/// combined with other error values.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::any(
///     // make the ! error from str_identifier
///     // compatible with the i32 error below
///     ab::infer_void_error(ab::str_identifier()),
///     // infer_void_parsed makes the ! value from
///     // error(..) compatible with the &str value
///     // from str_identifier()
///     ab::infer_void_parsed(ab::error(23)),
/// );
/// ```
#[inline]
pub fn infer_void_error<'a, Y, N, E, F>(parser: F) -> impl Fn(Input<'a>) -> PResult<Y, N, E>
where F: Fn(Input<'a>) -> PResult<Y, N, !> {
    move |input| match parser(input) {
        Ok(v) => Ok(v),
        Err(_) => panic!("infer_void_error unexpectedly received an error from the parser"),
    }
}

/// Produces a pass-through helper parser for sub-parsers returning `!` values.
///
/// This function takes a sub-parser returning a `!` value, but returns a parser with a generic
/// value type.  It can be used to counter type mismatch errors when parsers with `!` values are
/// combined with other value types.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::any(
///     // make the ! error from str_identifier
///     // compatible with the i32 error below
///     ab::infer_void_error(ab::str_identifier()),
///     // infer_void_parsed makes the ! value from
///     // error(..) compatible with the &str value
///     // from str_identifier()
///     ab::infer_void_parsed(ab::error(23)),
/// );
/// ```
#[inline]
pub fn infer_void_parsed<'a, Y, N, E, F>(parser: F) -> impl Fn(Input<'a>) -> PResult<Y, N, E>
where F: Fn(Input<'a>) -> PResult<!, N, E> {
    move |input| match parser(input) {
        Ok(ParseResult::Parsed(_)) =>
            panic!("infer_void_parsed unexpectedly received a value from the parser"),
        Ok(ParseResult::Failed(failed)) => Ok(ParseResult::Failed(failed)),
        Err(e) => Err(e),
    }
}

/// Produces a pass-through helper parser for sub-parsers returning `!` failures.
///
/// This function takes a sub-parser returning a `!` failure, but returns a parser with a generic
/// failure type.  It can be used to counter type mismatch errors when parsers with `!` failures
/// are combined with other failure types.
#[inline]
pub fn infer_void_failed<'a, Y, N, E, F>(parser: F) -> impl Fn(Input<'a>) -> PResult<Y, N, E>
where F: Fn(Input<'a>) -> PResult<Y, !, E> {
    move |input| match parser(input) {
        Ok(ParseResult::Failed(_)) =>
            panic!("infer_void_parsed unexpectedly received a failure from the parser"),
        Ok(ParseResult::Parsed(parsed)) => Ok(ParseResult::Parsed(parsed)),
        Err(e) => Err(e),
    }
}

/// Produces a parser that can turn failures into errors.
///
/// Takes a sub-parser and a mapping function. The mapping function will receive the failure
/// and its location.
///
/// If the mapping function returns an `Ok(_)` value, the result will continue to be a failure
/// with the same state and position, but with the new value.
///
/// If the mapping function returns an `Err(_)` value, the result will be an error containing
/// the new value.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// #[derive( Debug, PartialEq, Eq )]
/// struct MyError {
///     error: ab::NoIdentifier,
///     location: ab::Location,
/// }
///
/// let parser = ab::failed_lift(
///     ab::infer_void_error(ab::str_identifier()),
///     |error, location| Err(MyError {
///         error: error,
///         location: location,
///     }),
/// );
///
/// // parse failure
/// assert_eq!(
///     ab::get("23", &parser),
///     Err(ab::GetError::Error(MyError {
///         error: ab::NoIdentifier,
///         location: ab::Location {
///             line: 1,
///             column: 1,
///             position: 0,
///         },
///     }))
/// );
///
/// // successful parse
/// assert_eq!(
///     ab::get("foo", &parser),
///     Ok(("foo", ab::State::Incomplete, ""))
/// );
/// ```
pub fn failed_lift<'a, F, Y, N, E, M>(parser: F, mapper: M)
-> impl Fn(Input<'a>)
-> PResult<Y, N, E>
where F: Fn(Input<'a>) -> PResult<Y, N, E>, M: Fn(N, ::Location) -> Result<N, E> {
    move |input| {
        match parser(input) {
            Ok(ParseResult::Failed(failed)) => match mapper(failed.error, failed.location) {
                Ok(error) => Ok(ParseResult::new_failed(error, failed.state, failed.location)),
                Err(error) => Err(error),
            },
            other => other,
        }
    }
}

/// Produces a parser that can optionally produce an error from a parsed value.
///
/// Takes a sub-parser and a mapping function. The produced parser will produce errors
/// (not failed results) if the mapping function returns an `Err(_)` value. If an `Ok(_)`
/// value is returned, it is assumed to be the new parsed value. 
///
/// The mapping function receives the parsed value and the current location as arguments.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// #[derive( Debug, PartialEq, Eq )]
/// struct IdentifierSizeError {
///     len: usize,
///     location: ab::Location,
/// }
///
/// let parser = ab::verify(
///     ab::infer_void_error(ab::str_identifier()),
///     |value, location| if value.len() > 3 {
///         Err(IdentifierSizeError {
///             len: value.len(),
///             location: location,
///         })
///     } else {
///         Ok(value)
///     }
/// );
///
/// // parsed, but verify produces error
/// assert_eq!(
///     ab::get("barbaz", &parser),
///     Err(ab::GetError::Error(IdentifierSizeError {
///         len: 6,
///         location: ab::Location {
///             line: 1,
///             column: 1,
///             position: 0,
///         },
///     }))
/// );
///
/// // parsed, and passed the verify callback
/// assert_eq!(
///     ab::get("foo", &parser),
///     Ok(("foo", ab::State::Incomplete, ""))
/// );
///
/// // failed parse, verify callback not involved
/// assert_eq!(
///     ab::get("23", &parser),
///     Err(ab::GetError::Failed(
///         ab::NoIdentifier,
///         ab::State::Complete,
///         ab::Location {
///             line: 1,
///             column: 1,
///             position: 0,
///         },
///     ))
/// );
/// ```
pub fn verify<'a, F, Y, N, E, M>(parser: F, mapper: M)
-> impl Fn(Input<'a>)
-> PResult<Y, N, E>
where F: Fn(Input<'a>) -> PResult<Y, N, E>, M: Fn(Y, ::Location) -> Result<Y, E> {
    move |input| {
        match parser(input) {
            Ok(ParseResult::Parsed(parsed)) => match mapper(parsed.value, input.location()) {
                Ok(value) => Ok(ParseResult::new_parsed(value, parsed.state, parsed.rest)),
                Err(error) => Err(error),
            },
            other => other,
        }
    }
}

/// Produces a parser applying a mapping function to error values.
///
/// Allows mapping from one error type (or value) into another via a mapping function.
///
/// The mapping function will receive the error and current location as arguments.
///
/// # Examples
/// ```rust
/// # #![feature( never_type )]
/// use absorb as ab;
///
/// #[derive( Debug, PartialEq, Eq )]
/// struct MyListError {
///     error: ab::ListError<!, !>,
///     location: ab::Location,
/// }
///
/// let parser = ab::error_map(
///     ab::optional(ab::list(
///         ab::char_exact(','),
///         ab::str_identifier(),
///         ab::ListLimit::Limited(3),
///     )),
///     |error, location| MyListError {
///         error: error,
///         location: location,
///     },
/// );
///
/// assert_eq!(
///     ab::get("foo,bar,baz,qux", &parser),
///     Err(ab::GetError::Error(MyListError {
///         error: ab::ListError::LimitExceeded {
///             limit: 3,
///         },
///         location: ab::Location {
///             line: 1,
///             column: 1,
///             position: 0,
///         },
///     }))
/// );
/// ```
pub fn error_map<'a, F, Y, N, E, M, X>(parser: F, mapper: M)
-> impl Fn(Input<'a>)
-> PResult<Y, N, X>
where F: Fn(Input<'a>) -> PResult<Y, N, E>, M: Fn(E, ::Location) -> X {
    move |input| parser(input).map_err(|error| mapper(error, input.location()))
}

/// Produces a parser applying a mapping function to failed results.
///
/// Allows mapping from one failure type (or value) to another via a mapping function.
///
/// The mapping function will receive the failure value as argument.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// #[derive( Debug, PartialEq, Eq )]
/// struct VeryImportantIdentifierError {
///     inner: ab::NoIdentifier,
/// }
///
/// let parser = ab::failed_map(
///     ab::str_identifier(),
///     |failure_value| VeryImportantIdentifierError {
///         inner: failure_value,
///     },
/// );
///
/// assert_eq!(
///     ab::get("23", &parser),
///     Err(ab::GetError::Failed(
///         VeryImportantIdentifierError {
///             inner: ab::NoIdentifier,
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
pub fn failed_map<'a, F, Y, N, E, M, X>(parser: F, mapper: M)
-> impl Fn(Input<'a>)
-> PResult<Y, X, E>
where F: Fn(Input<'a>) -> PResult<Y, N, E>, M: Fn(N) -> X {
    move |input| parser(input).map(|output| output.map_failed(&mapper))
}

/// Produces a parser applying a mapping function to parsed values.
///
/// Allows mapping from one successful parse result type (or value) to another via a
/// mapping function.
///
/// The mapping function receives the parse result value and the current location as arguments.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// #[derive( Debug, PartialEq, Eq )]
/// struct IdentifierWithLocation {
///     identifier: String,
///     location: ab::Location,
/// }
///
/// let parser = ab::parsed_map(
///     ab::str_identifier(),
///     |value, location| IdentifierWithLocation {
///         identifier: value.into(),
///         location: location,
///     },
/// );
///
/// assert_eq!(
///     ab::get("foo", &parser),
///     Ok((
///         IdentifierWithLocation {
///             identifier: "foo".into(),
///             location: ab::Location {
///                 line: 1,
///                 column: 1,
///                 position: 0,
///             },
///         },
///         ab::State::Incomplete,
///         "",
///     ))
/// );
/// ```
pub fn parsed_map<'a, F, Y, N, E, M, X>(parser: F, mapper: M)
-> impl Fn(Input<'a>)
-> PResult<X, N, E>
where F: Fn(Input<'a>) -> PResult<Y, N, E>, M: Fn(Y, ::Location) -> X {
    move |input| parser(input).map(|output| output.map_parsed(|v| mapper(v, input.location())))
}

/// Produces a parser applying mapping functions to parsed and failed result values.
///
/// Takes a sub-parser, and one mapping function each for parsed and failed result values.
/// It combines the `parsed_map` and `failed_map` parsers into one.
///
/// The mapping function for successfully parsed results receives the value and current location
/// as arguments.
///
/// The mapping function for failed parse results receives the failure value as argument.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// #[derive( Debug, PartialEq, Eq )]
/// struct VeryImportantIdentifierError {
///     inner: ab::NoIdentifier,
/// }
///
/// #[derive( Debug, PartialEq, Eq )]
/// struct IdentifierWithLocation {
///     identifier: String,
///     location: ab::Location,
/// }
///
/// let parser = ab::map(
///     ab::str_identifier(),
///     |value, location| IdentifierWithLocation {
///         identifier: value.into(),
///         location: location,
///     },
///     |failure_value| VeryImportantIdentifierError {
///         inner: failure_value,
///     },
/// );
///
/// // mapping successful parse
/// assert_eq!(
///     ab::get("foo", &parser),
///     Ok((
///         IdentifierWithLocation {
///             identifier: "foo".into(),
///             location: ab::Location {
///                 line: 1,
///                 column: 1,
///                 position: 0,
///             },
///         },
///         ab::State::Incomplete,
///         "",
///     ))
/// );
///
/// // mapping failed parse
/// assert_eq!(
///     ab::get("23", &parser),
///     Err(ab::GetError::Failed(
///         VeryImportantIdentifierError {
///             inner: ab::NoIdentifier,
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
pub fn map<'a, Y, N, E, F, MY, MN, NY, NN>(parser: F, p_map: MY, f_map: MN)
-> impl Fn(Input<'a>)
-> PResult<NY, NN, E>
    where
        F: Fn(Input<'a>) -> PResult<Y, N, E>,
        MY: Fn(Y, ::Location) -> NY,
        MN: Fn(N) -> NN {
    failed_map(parsed_map(parser, p_map), f_map)
}

/// Produces a zero-length parser returning the current location as value.
///
/// This parser consumes zero input, never fails, and never returns an error.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
/// let parser = ab::take_right(
///     ab::str_whitespace(),
///     ab::location(),
/// );
///
/// assert_eq!(
///     ab::get("  foo", &parser),
///     Ok((
///         ab::Location {
///             line: 1,
///             column: 3,
///             position: 2,
///         },
///         ab::State::Complete,
///         "foo",
///     ))
/// );
/// ```
#[inline]
pub fn location() -> impl Fn(Input) -> PResult<::Location, !, !> {
    |input| Ok(ParseResult::new_parsed(input.location(), State::Complete, input))
}

/// Produces a zero-length parser generating errors by cloning.
///
/// The passed in error value will be closed over and kept alive until the closure is
/// destroyed. On every invocation of the parser, a new error value will be cloned.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// #[derive( Debug, Clone, PartialEq, Eq )]
/// struct NothingFound;
///
/// let parser = ab::any(
///     ab::infer_void_error(ab::str_identifier()),
///     ab::infer_void_parsed(ab::error(NothingFound)),
/// );
///
/// assert_eq!(
///     ab::get("23", &parser),
///     Err(ab::GetError::Error(NothingFound))
/// );
/// ```
#[inline]
pub fn error<E>(error: E) -> impl Fn(Input) -> PResult<!, !, E>
where E: Clone {
    move |_input| Err(error.clone())
}

/// Produces a zero-length parser generating errors from a closure.
///
/// The passed function will be used to produce new errors when the parser is invoked. The
/// function will receive the current location as argument.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// #[derive( Debug, PartialEq, Eq )]
/// struct NothingFound {
///     at: ab::Location,
/// }
///
/// let parser = ab::any(
///     ab::infer_void_error(ab::str_identifier()),
///     ab::infer_void_parsed(
///         ab::error_from(|location| NothingFound {
///             at: location,
///         }),
///     ),
/// );
///
/// assert_eq!(
///     ab::get("23", &parser),
///     Err(ab::GetError::Error(NothingFound {
///         at: ab::Location {
///             line: 1,
///             column: 1,
///             position: 0,
///         },
///     }))
/// );
/// ```
#[inline]
pub fn error_from<E, F>(from: F) -> impl Fn(Input) -> PResult<!, !, E>
where F: Fn(::Location) -> E {
    move |input| Err(from(input.location()))
}

/// Produces a zero-length parser generating parse failures by cloning.
///
/// The passed in failure value will be closed over and kept alive until the closure is
/// destroyed. On every invocation of the parser, a new failure value will be cloned.
///
/// This parser producer function also takes the `State` value indicating completeness
/// of the result as argument.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// #[derive( Debug, Clone, PartialEq, Eq )]
/// struct NothingValid;
///
/// let parser = ab::any(
///     ab::str_identifier(),
///     ab::infer_void_parsed(ab::fail(
///         ab::State::Complete,
///         NothingValid,
///     )),
/// );
///
/// assert_eq!(
///     ab::get("23", &parser),
///     Err(ab::GetError::Failed(
///         NothingValid,
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
pub fn fail<N>(state: State, error: N) -> impl Fn(Input) -> PResult<!, N, !>
where N: Clone {
    move |input| Ok(ParseResult::new_failed(error.clone(), state, input))
}

/// Produces a zero-length parser generating parse failures from a closure.
///
/// The passed function will be used to produce new failure values when the parser is invoked.
///
/// This parser producer function also takes the `State` value indicating completeness
/// of the result as argument.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// #[derive( Debug, PartialEq, Eq )]
/// struct NothingValid;
///
/// let parser = ab::any(
///     ab::str_identifier(),
///     ab::infer_void_parsed(ab::fail_from(
///         ab::State::Complete,
///         || NothingValid,
///     )),
/// );
///
/// assert_eq!(
///     ab::get("23", &parser),
///     Err(ab::GetError::Failed(
///         NothingValid,
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
pub fn fail_from<N, F>(state: State, from: F) -> impl Fn(Input) -> PResult<!, N, !>
where F: Fn() -> N {
    move |input| Ok(ParseResult::new_failed(from(), state, input))
}

/// Produces a zero-length parser generating successful parse values by cloning.
///
/// The passed in value will be closed over and kept alive until the closure is
/// destroyed. On every invocation of the parser, a new value will be cloned.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::any(
///     ab::str_identifier(),
///     ab::value("default"),
/// );
///
/// assert_eq!(
///     ab::get("23", &parser),
///     Ok(("default", ab::State::Complete, "23"))
/// );
///
/// assert_eq!(
///     ab::get("foo", &parser),
///     Ok(("foo", ab::State::Incomplete, ""))
/// );
/// ```
#[inline]
pub fn value<Y>(value: Y) -> impl Fn(Input) -> PResult<Y, !, !>
where Y: Clone {
    move |input| Ok(ParseResult::new_parsed(value.clone(), State::Complete, input))
}

/// Produces a zero-length parser generating successful parse values from a closure.
///
/// The passed function will be used to produce new success values when the parser is invoked.
///
/// The function will receive the current location as argument.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// #[derive( Debug, PartialEq, Eq )]
/// struct IdentifierWithLocation {
///     identifier: String,
///     location: ab::Location,
/// }
///
/// let parser = ab::any(
///     ab::parsed_map(
///         ab::str_identifier(),
///         |value, location| IdentifierWithLocation {
///             identifier: value.into(),
///             location: location,
///         },
///     ),
///     ab::value_from(
///         |location| IdentifierWithLocation {
///             identifier: "default".into(),
///             location: location,
///         },
///     ),
/// );
///
/// assert_eq!(
///     ab::get("23", &parser),
///     Ok((
///         IdentifierWithLocation {
///             identifier: "default".into(),
///             location: ab::Location {
///                 line: 1,
///                 column: 1,
///                 position: 0,
///             },
///         },
///         ab::State::Complete,
///         "23",
///     ))
/// );
///
/// assert_eq!(
///     ab::get("foo", &parser),
///     Ok((
///         IdentifierWithLocation {
///             identifier: "foo".into(),
///             location: ab::Location {
///                 line: 1,
///                 column: 1,
///                 position: 0,
///             },
///         },
///         ab::State::Incomplete,
///         "",
///     ))
/// );
/// ```
#[inline]
pub fn value_from<Y, F>(from: F) -> impl Fn(Input) -> PResult<Y, !, !>
where F: Fn(::Location) -> Y {
    move |input| Ok(ParseResult::new_parsed(from(input.location()), State::Complete, input))
}

/// Produces a parser that allows mapping between parsed and failed results.
///
/// This parser producer takes a sub-parser and two functions: A function handling successful
/// parse results, and a function handling failed parse results. Errors will be passed through
/// untouched.
///
/// If the function corresponding with the result from the sub-parser returns an `Ok(_)` value
/// it will be used as a successful parse result, while an `Err(_)` value will be consiered
/// a failed parse result.
///
/// Both functions will additionally receive the current location as argument.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// #[derive( Debug, PartialEq, Eq )]
/// enum CustomFail {
///     NoIdentifier(ab::Location),
///     TooShort(ab::Location),
/// }
///
/// let parser = ab::fmap(
///     ab::str_identifier(),
///     |parsed, location|
///         if parsed.len() > 2 {
///             Ok(parsed)
///         } else {
///             Err(CustomFail::TooShort(location))
///         },
///     |_failed, location|
///         Err(CustomFail::NoIdentifier(location)),
/// );
///
/// assert_eq!(
///     ab::get("a", &parser),
///     Err(ab::GetError::Failed(
///         CustomFail::TooShort(ab::Location {
///             line: 1,
///             column: 1,
///             position: 0,
///         }),
///         ab::State::Incomplete,
///         ab::Location {
///             line: 1,
///             column: 1,
///             position: 0,
///         },
///     ))
/// );
///
/// assert_eq!(
///     ab::get("23", &parser),
///     Err(ab::GetError::Failed(
///         CustomFail::NoIdentifier(ab::Location {
///             line: 1,
///             column: 1,
///             position: 0,
///         }),
///         ab::State::Complete,
///         ab::Location {
///             line: 1,
///             column: 1,
///             position: 0,
///         },
///     ))
/// );
///
/// assert_eq!(
///     ab::get("foo", &parser),
///     Ok(("foo", ab::State::Incomplete, ""))
/// );
/// ```
pub fn fmap<'a, Y, N, E, F, MY, MN, NY, NN>(parser: F, p_map: MY, f_map: MN)
-> impl Fn(Input<'a>)
-> PResult<NY, NN, E>
    where
        F: Fn(Input<'a>) -> PResult<'a, Y, N, E>,
        MY: Fn(Y, ::Location) -> Result<NY, NN>,
        MN: Fn(N, ::Location) -> Result<NY, NN> {
    move |input| {
        let loc = input.location();
        parser(input).map(|result| match result {
            ParseResult::Parsed(Parsed { value, state, rest }) => match p_map(value, loc) {
                Ok(new) => ParseResult::new_parsed(new, state, rest),
                Err(err) => ParseResult::new_failed(err, state, input),
            },
            ParseResult::Failed(Failed { error, state, location }) => match f_map(error, loc) {
                Ok(new) => ParseResult::new_parsed(new, state, input),
                Err(err) => ParseResult::new_failed(err, state, location),
            },
        })
    }
}

#[cfg(test)]
mod tests {

    #[derive( Debug, Clone, PartialEq, Eq )]
    struct Wrap<T>(T);

    #[test]
    fn not() {
        test!(super::not(::str_identifier()),
            "foo" => (err?: "foo", (0, 1, 1)),
            "23" => (ok: (), "23"),
            "" => (ok?: (), ""),
        );
    }

    #[test]
    fn verify() {
        test!(
            super::verify(
                ::infer_void_error(::str_identifier()),
                |v, l| if v == "foo" { Err(l) } else { Ok(v) },
            ),
            "bar" => (ok?: "bar", ""),
            "foo" => (fatal: ::Location { position: 0, line: 1, column: 1 }),
            "23" => (err: ::NoIdentifier, (0, 1, 1)),
        );
    }

    #[test]
    fn failed_lift() {
        test!(
            super::failed_lift(
                ::infer_void_error(::str_identifier()),
                |e, _| Ok::<_, !>(e),
            ),
            "foo" => (ok?: "foo", ""),
            "23" => (err: ::NoIdentifier, (0, 1, 1)),
        );
        test!(
            super::failed_lift(
                ::infer_void_error(::str_identifier()),
                |e, l| Err(Wrap((e, l))),
            ),
            "foo" => (ok?: "foo", ""),
            "23" => (fatal: Wrap((
                ::NoIdentifier,
                ::Location { position: 0, line: 1, column: 1 },
            ))),
        );
    }

    #[test]
    fn infer_void_error() {
        test!(
            ::any(
                super::infer_void_error(::str_identifier()),
                super::infer_void_parsed(::error(23)),
            ),
            "42" => (fatal: 23),
            "foo" => (ok?: "foo", ""),
        );
    }

    #[test]
    fn infer_void_failed() {
        fn source(flag: bool)
        -> impl Fn(::Input)
        -> ::PResult<&str, !, &'static str> {
            move |input| {
                if flag {
                    Ok(::ParseResult::new_parsed(input.slice(), ::State::Complete, input))
                }
                else { Err("fail") }
            }
        }
        fn both<'a, L, R, YL, YR, N, EL, ER>(_left: L, right: R)
        -> impl Fn(::Input<'a>) -> ::PResult<'a, YR, N, ER>
            where
                L: Fn(::Input<'a>) -> ::PResult<'a, YL, N, EL>,
                R: Fn(::Input<'a>) -> ::PResult<'a, YR, N, ER> {
            right
        }
        test!(
            both(
                ::str_identifier(),
                super::infer_void_failed(source(true)),
            ),
            "23" => (ok: "23", "23"),
        );
        test!(
            both(
                ::str_identifier(),
                super::infer_void_failed(source(false)),
            ),
            "23" => (fatal: "fail"),
        );
    }

    #[test]
    fn infer_void_parsed() {
        fn source(flag: bool)
        -> impl Fn(::Input)
        -> ::PResult<!, i32, &'static str> {
            move |input| {
                if flag { Ok(::ParseResult::new_failed(23, ::State::Complete, input)) }
                else { Err("fail") }
            }
        }
        test!(
            ::any(
                super::infer_void_error(::str_identifier()),
                super::infer_void_parsed(source(true)),
            ),
            "" => (err?: 23, (0, 1, 1)),
        );
        test!(
            ::any(
                super::infer_void_error(::str_identifier()),
                super::infer_void_parsed(source(false)),
            ),
            "" => (fatal: "fail"),
        );
    }

    #[test]
    fn fmap() {
        test!(
            super::fmap(
                ::take_right(::str_whitespace(), ::str_identifier()),
                |value, loc| {
                    assert_eq!(loc.line, 1);
                    if value == "foo" { Ok(23) } else { Err(42) }
                },
                |error, loc| {
                    assert_eq!(loc.line, 1);
                    if let ::PairError::Left(_) = error { Ok(33) } else { Err(52) }
                },
            ),
            "  foo" => (ok?: 23, ""),
            "  foo " => (ok: 23, " "),
            "  bar" => (err?: 42, (0, 1, 1)),
            "  bar " => (err: 42, (0, 1, 1)),
            "" => (ok?: 33, ""),
            "foo" => (ok: 33, "foo"),
            "  " => (err?: 52, (2, 1, 3)),
            "  !" => (err: 52, (2, 1, 3)),
        );
    }

    #[test]
    fn map() {
        test!(
            super::map(::str_identifier(),
                |v, l| {
                    assert_eq!(v, "foo");
                    assert_eq!(l.line, 1);
                    23
                },
                |e| {
                    assert_eq!(e, ::NoIdentifier);
                    42
                },
            ),
            "foo" => (ok?: 23, ""),
            "foo!" => (ok: 23, "!"),
            "23" => (err: 42, (0, 1, 1)),
            "" => (err?: 42, (0, 1, 1)),
        );
    }

    #[test]
    fn location() {
        let loc = |p, l, c| ::Location { position: p, line: l, column: c };
        test!(
            ::take_right(
                ::optional(::str_whitespace()),
                ::take_right(::str_identifier(), super::location()),
            ),
            "foo." => (ok: loc(3, 1, 4), "."),
            "    foo." => (ok: loc(7, 1, 8), "."),
            "  \n\t  \n  foo." => (ok: loc(12, 3, 6), "."),
        );
    }

    #[test]
    fn error_from() {
        test!(
            super::error_from(|l| Wrap(l)),
            "" => (fatal: Wrap(::Location { position: 0, line: 1, column: 1 })),
        );
    }

    #[test]
    fn error() {
        test!(super::error(23), "" => (fatal: 23));
    }

    #[test]
    fn value_from() {
        let loc = ::Location { position: 0, line: 1, column: 1 };
        test!(super::value_from(|l| (23, l)),
            "" => (ok: (23, loc), ""),
            " " => (ok: (23, loc), " "),
        );
        test!(
            ::any(::str_identifier(), super::value_from(|l| {
                assert_eq!(l, loc);
                "new"
            })),
            "foo" => (ok?: "foo", ""),
            "foo " => (ok: "foo", " "),
            "" => (ok?: "new", ""),
            " " => (ok: "new", " "),
        );
    }

    #[test]
    fn value() {
        test!(super::value(23),
            "" => (ok: 23, ""),
            " " => (ok: 23, " "),
        );
        test!(::any(::str_identifier(), super::value("new")),
            "foo" => (ok?: "foo", ""),
            "foo " => (ok: "foo", " "),
            "" => (ok?: "new", ""),
            " " => (ok: "new", " "),
        );
    }

    #[test]
    fn fail_from() {
        test!(super::fail_from(::State::Complete, || 23),
            "" => (err: 23, (0, 1, 1)),
            "23" => (err: 23, (0, 1, 1)),
        );
        test!(super::fail_from(::State::Incomplete, || 23),
            "" => (err?: 23, (0, 1, 1)),
            "23" => (err?: 23, (0, 1, 1)),
        );
        test!(
            ::any(
                ::str_exact("foo"),
                ::infer_void_parsed(super::fail_from(::State::Complete, || 23)),
            ),
            "foo" => (ok: "foo", ""),
            "bar" => (err: 23, (0, 1, 1)),
            "fo" => (err?: 23, (0, 1, 1)),
            "" => (err?: 23, (0, 1, 1)),
        );
        test!(
            ::any(
                ::str_exact("foo"),
                ::infer_void_parsed(super::fail_from(::State::Incomplete, || 23)),
            ),
            "foo" => (ok: "foo", ""),
            "bar" => (err?: 23, (0, 1, 1)),
            "fo" => (err?: 23, (0, 1, 1)),
            "" => (err?: 23, (0, 1, 1)),
        );
    }

    #[test]
    fn fail() {
        test!(super::fail(::State::Complete, 42),
            "" => (err: 42, (0, 1, 1)),
            "23" => (err: 42, (0, 1, 1)),
        );
        test!(super::fail(::State::Incomplete, 42),
            "" => (err?: 42, (0, 1, 1)),
            "23" => (err?: 42, (0, 1, 1)),
        );
        test!(
            ::any(
                ::str_exact("foo"),
                ::infer_void_parsed(super::fail(::State::Complete, 42)),
            ),
            "foo" => (ok: "foo", ""),
            "bar" => (err: 42, (0, 1, 1)),
            "fo" => (err?: 42, (0, 1, 1)),
            "" => (err?: 42, (0, 1, 1)),
        );
        test!(
            ::any(
                ::str_exact("foo"),
                ::infer_void_parsed(super::fail(::State::Incomplete, 42)),
            ),
            "foo" => (ok: "foo", ""),
            "bar" => (err?: 42, (0, 1, 1)),
            "fo" => (err?: 42, (0, 1, 1)),
            "" => (err?: 42, (0, 1, 1)),
        );
    }

    #[test]
    fn error_map() {
        fn err_source(_: ::Input) -> ::PResult<!, !, &'static str> { Err("fail") }
        test!(super::error_map(err_source, |e, l| Wrap((e, l))),
            "" => (fatal: Wrap(("fail", ::Location { position: 0, line: 1, column: 1 }))),
        );
        test!(super::error_map(::str_identifier(), |_, _| panic!("should not map")),
            "foo" => (ok?: "foo", ""),
        );
    }

    #[test]
    fn value_map() {
        let loc = ::Location { position: 0, line: 1, column: 1 };
        test!(super::parsed_map(::str_identifier(), |v, l| Wrap((v, l))),
            "foo" => (ok?: Wrap(("foo", loc)), ""),
            "foo " => (ok: Wrap(("foo", loc)), " "),
            "" => (err?: ::NoIdentifier, (0, 1, 1)),
            "23" => (err: ::NoIdentifier, (0, 1, 1)),
        );
    }

    #[test]
    fn failed_map() {
        test!(
            super::failed_map(::str_identifier(), |e| {
                assert_eq!(e, ::NoIdentifier);
                Wrap(e)
            }),
            "foo" => (ok?: "foo", ""),
            "foo " => (ok: "foo", " "),
            "" => (err?: Wrap(::NoIdentifier), (0, 1, 1)),
            "23" => (err: Wrap(::NoIdentifier), (0, 1, 1)),
        );
    }
}
