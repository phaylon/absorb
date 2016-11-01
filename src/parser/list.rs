
use std::fmt;

use ::{ PResult, ParseResult, Parsed, Failed, Input };

/// Error for accumulating parsers.
#[derive( Debug, Copy, Clone, PartialEq, Eq )]
pub enum AccumulatorError<IE, SE, AE> {
    /// The item parser returned an error at the given index.
    ItemError {
        /// The error returned from the item sub-parser.
        error: IE,
        /// The index at which the sub-parser returned the error.
        index: usize,
    },
    /// The separator parser returned an error at the given index.
    SeparatorError {
        /// The error returned from the separator sub-parser.
        error: SE,
        /// The index at which the sub-parser returned the error.
        index: usize,
    },
    /// The accumulating callback indicated an error by returning an `Err(_)` result
    /// with the given error at the given index.
    CallbackError {
        /// The error returned from the accumulator function.
        error: AE,
        /// The index at which the accumulator function returned the error
        index: usize,
    },
}

impl<IE, SE, AE> fmt::Display for AccumulatorError<IE, SE, AE>
where IE: fmt::Display, SE: fmt::Display, AE: fmt::Display {

    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            AccumulatorError::ItemError { ref error, index } =>
                write!(out, "Item Error (index {}): {}", index, error),
            AccumulatorError::SeparatorError { ref error, index } =>
                write!(out, "Separator Error (index {}): {}", index, error),
            AccumulatorError::CallbackError { ref error, index } =>
                write!(out, "Callback Error (index {}): {}", index, error),
        }
    }
}

/// Error for the list parser.
#[derive( Debug, Copy, Clone, PartialEq, Eq )]
pub enum ListError<IE, SE> {
    /// The item parser returned an error at the given index.
    ItemError {
        /// The error returned from the item sub-parser.
        error: IE,
        /// The index at which the sub-parser returned the error.
        index: usize,
    },
    /// The separator parser returned an error at the given index.
    SeparatorError {
        /// The error returned from the separator sub-parser.
        error: SE,
        /// The index at which the sub-parser returned the error.
        index: usize,
    },
    /// An explicit or implicit item count limit has been reached.
    LimitExceeded {
        /// The limit that was exceeded.
        limit: usize,
    },
}

impl<IE, SE> fmt::Display for ListError<IE, SE>
where IE: fmt::Display, SE: fmt::Display {

    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ListError::ItemError { ref error, index } =>
                write!(out, "Item Error (index {}): {}", index, error),
            ListError::SeparatorError { ref error, index } =>
                write!(out, "Separator Error (index {}): {}", index, error),
            ListError::LimitExceeded { limit } =>
                write!(out, "List limit ({}) was exceeded", limit),
        }
    }
}

/// Size limit for list accumulation.
#[derive( Debug, Copy, Clone, PartialEq, Eq )]
pub enum ListLimit {
    /// No limit.
    Unlimited,
    /// Limited to a specific number.
    Limited(usize),
}

/// Produces a general accumulation parser without per-item errors.
///
/// Parsers produced by this function the same way like the ones produced by `accumulate`.
/// The only difference is that this version doesn't include per-item error handling.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::accumulate_flat(
///     ab::char_exact(','),
///     ab::char_digit(10).unwrap(),
///     |_location| 0,
///     |sum, value, _location| sum + value.to_digit(10).unwrap(),
/// );
///
/// assert_eq!(
///     ab::get("2,3,4,5,6", &parser),
///     Ok((
///         20,
///         ab::State::Incomplete,
///         "",
///     ))
/// );
/// ```
#[inline(never)]
pub fn accumulate_flat<'a, V, VF, AF, SF, IF, SY, SN, IY, IN, SE, IE>(
    separator: SF,
    item: IF,
    init: VF,
    accumulator: AF,
)
-> impl Fn(Input<'a>)
-> PResult<V, IN, AccumulatorError<IE, SE, !>>
    where
        SF: Fn(Input<'a>) -> PResult<SY, SN, SE>,
        IF: Fn(Input<'a>) -> PResult<IY, IN, IE>,
        VF: Fn(::Location) -> V,
        AF: Fn(V, IY, ::Location) -> V {
    accumulate(separator, item, init, move |v, y, l| Ok(accumulator(v, y, l)))
}

/// Produces a general accumulation parser.
///
/// A parser accumulating one or more values parsed by the `item` sub-parser, optionally
/// separated by the `separator` sub-parser.
///
/// The `init` function is used to construct the initial accumulator value. It receives
/// the current location as argument.
///
/// The `accumulator` function is used to accumulate the parsed values. It receives the
/// last (or initial) accumulator value, the current parsed result value, and the location
/// where the item was parsed as arguments. It has to return a new accumulator value as
/// `Ok(_)` result on success, and `Err(_)` if any error occured. Errors from the accumulator
/// function will be returned inside the `AccumulatorError::CallbackError` variant.
///
/// The kept index will wrap around on overflow.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
///
/// let parser = ab::accumulate(
///     ab::char_exact(','),
///     ab::char_digit(10).unwrap(),
///     |_location| 0,
///     |sum, value, _location| match value.to_digit(10) {
///         Some(value) => Ok(sum + value),
///         None => Err("unexpected invalid digit"),
///     },
/// );
///
/// assert_eq!(
///     ab::get("2,3,4,5,6", &parser),
///     Ok((
///         20,
///         ab::State::Incomplete,
///         "",
///     ))
/// );
/// ```
#[inline(never)]
pub fn accumulate<'a, V, VF, AF, AE, SF, IF, SY, SN, IY, IN, SE, IE>(
    separator: SF,
    item: IF,
    init: VF,
    accumulator: AF,
)
-> impl Fn(Input<'a>)
-> PResult<V, IN, AccumulatorError<IE, SE, AE>>
    where
        SF: Fn(Input<'a>) -> PResult<SY, SN, SE>,
        IF: Fn(Input<'a>) -> PResult<IY, IN, IE>,
        VF: Fn(::Location) -> V,
        AF: Fn(V, IY, ::Location) -> Result<V, AE> {
    move |input| {
        let (mut rest, mut accumulated, mut all_state) = {
            let Parsed { value, rest, state } = match item(input) {
                Err(error) => return Err(AccumulatorError::ItemError { error: error, index: 0 }),
                Ok(ParseResult::Failed(failed)) => return Ok(ParseResult::Failed(failed)),
                Ok(ParseResult::Parsed(parsed)) => parsed,
            };
            let prepared = match accumulator(init(input.location()), value, input.location()) {
                Ok(value) => value,
                Err(error) =>
                    return Err(AccumulatorError::CallbackError { error: error, index: 0 }),
            };
            (rest, prepared, state)
        };
        let mut index = 1;
        loop {
            let sep_rest = match separator(rest) {
                Err(error) => return Err(AccumulatorError::SeparatorError {
                    error: error,
                    index: index - 1,
                }),
                Ok(ParseResult::Parsed(Parsed { rest: sep_rest, state: sep_state, .. })) => {
                    all_state = all_state.merge(sep_state);
                    sep_rest
                },
                Ok(ParseResult::Failed(Failed { state: sep_state, .. })) => {
                    all_state = all_state.merge(sep_state);
                    break;
                },
            };
            rest = match item(sep_rest) {
                Err(error) =>
                    return Err(AccumulatorError::ItemError { error: error, index: index }),
                Ok(ParseResult::Parsed(Parsed { rest: it_rest, state: it_state, value })) => {
                    accumulated = match accumulator(accumulated, value, sep_rest.location()) {
                        Ok(new) => new,
                        Err(error) => return Err(AccumulatorError::CallbackError {
                            error: error,
                            index: index,
                        }),
                    };
                    all_state = all_state.merge(it_state);
                    it_rest
                },
                Ok(ParseResult::Failed(Failed { state: item_state, .. })) => {
                    all_state = all_state.merge(item_state);
                    break;
                },
            };
            index = index.wrapping_add(1);
        }
        Ok(ParseResult::new_parsed(accumulated, all_state, rest))
    }
}

/// Produces an accumulating parser specialized for `Vec<_>` results.
///
/// A parser collecting one or more values parsed by the `item` sub-parser, separated
/// by the `separator` sub-parser.
///
/// The `limit` parameter specifies the maximum number of items to collect before a
/// `ListError::LimitExceeded` value will be returned.
///
/// # Examples
///
/// ```rust
/// use absorb as ab;
/// let parser = ab::list(
///     ab::char_exact(','),
///     ab::str_identifier(),
///     ab::ListLimit::Limited(2048),
/// );
///
/// assert_eq!(
///     ab::get("foo,bar,baz", &parser),
///     Ok((
///         vec!["foo", "bar", "baz"],
///         ab::State::Incomplete,
///         "",
///     ))
/// );
/// ```
pub fn list<'a, SF, IF, SY, SN, IY, IN, SE, IE>(separator: SF, item: IF, limit: ListLimit)
-> impl Fn(Input<'a>)
-> PResult<'a, Vec<IY>, IN, ListError<IE, SE>>
    where
        SF: Fn(Input<'a>) -> PResult<'a, SY, SN, SE>,
        IF: Fn(Input<'a>) -> PResult<'a, IY, IN, IE> {
    struct HitLimit(usize);
    ::error_map(
        accumulate(separator, item, |_| Vec::new(), move |mut items, item, _| {
            if let ListLimit::Limited(limit) = limit {
                if limit == items.len() {
                    return Err(HitLimit(limit));
                }
            }
            items.push(item);
            Ok(items)
        }),
        |error, _| match error {
            AccumulatorError::CallbackError { error: HitLimit(limit), .. } =>
                ListError::LimitExceeded { limit: limit },
            AccumulatorError::ItemError { error, index } =>
                ListError::ItemError { error: error, index: index },
            AccumulatorError::SeparatorError { error, index } =>
                ListError::SeparatorError { error: error, index: index },
        },
    )
}

#[cfg(test)]
mod tests {

    #[test]
    fn accumulate_flat() {
        test!(
            super::accumulate_flat(
                ::str_whitespace(),
                ::char_any(),
                |loc| (vec![loc], 0),
                |(mut locs, sum), item, loc| {
                    locs.push(loc);
                    (locs, sum + item.len_utf8())
                },
            ),
            "a b c" => (ok?: (vec![
                ::Location { position: 0, line: 1, column: 1 },
                ::Location { position: 0, line: 1, column: 1 },
                ::Location { position: 2, line: 1, column: 3 },
                ::Location { position: 4, line: 1, column: 5 },
            ], 3), ""),
            "ab" => (ok: (vec![
                ::Location { position: 0, line: 1, column: 1 },
                ::Location { position: 0, line: 1, column: 1 },
            ], 1), "b"),
        );
    }

    #[test]
    fn accumulate() {
        let cb_err: super::AccumulatorError<!, !, char> =
            super::AccumulatorError::CallbackError { error: 'x', index: 2 };
        test!(
            super::accumulate(
                ::str_whitespace(),
                ::char_any(),
                |loc| (vec![loc], 0),
                |(mut locs, sum), item, loc|
                    if item == 'x' { Err(item) } else {
                        locs.push(loc);
                        Ok((locs, sum + item.len_utf8()))
                    },
            ),
            "a b c" => (ok?: (vec![
                ::Location { position: 0, line: 1, column: 1 },
                ::Location { position: 0, line: 1, column: 1 },
                ::Location { position: 2, line: 1, column: 3 },
                ::Location { position: 4, line: 1, column: 5 },
            ], 3), ""),
            "a b x" => (fatal: cb_err),
            "ab" => (ok: (vec![
                ::Location { position: 0, line: 1, column: 1 },
                ::Location { position: 0, line: 1, column: 1 },
            ], 1), "b"),
        );
    }

    #[test]
    fn list() {
        test!(super::list(::char_exact('.'), ::char_any(), super::ListLimit::Unlimited),
            "" => (err?: ::NoChar, (0, 1, 1)),
            "a" => (ok?: vec!['a'], ""),
            "a." => (ok?: vec!['a'], "."),
            "ab" => (ok: vec!['a'], "b"),
            "a.b" => (ok?: vec!['a', 'b'], ""),
            "a.b." => (ok?: vec!['a', 'b'], "."),
            "a.b.cd" => (ok: vec!['a', 'b', 'c'], "d"),
        );
        {
            let limited =
                super::list(::char_exact('.'), ::char_any(), super::ListLimit::Limited(2));
            let err_limited = super::ListError::LimitExceeded { limit: 2 };
            test!(limited, "a.b.c" => (fatal: err_limited));
        }
        {
            let limit = super::ListLimit::Limited(2);
            let fail = super::list(
                super::list(::nothing(), ::char_exact('.'), limit),
                super::list(::nothing(), ::char_exact('x'), limit),
                super::ListLimit::Unlimited,
            );
            let err_sep = super::ListError::SeparatorError {
                error: super::ListError::LimitExceeded { limit: 2 },
                index: 2,
            };
            let err_item = super::ListError::ItemError {
                error: super::ListError::LimitExceeded { limit: 2 },
                index: 2,
            };
            test!(&fail,
                "x.x.x " => (ok: vec![vec!['x'], vec!['x'], vec!['x']], " "),
                "x.x.x...x " => (fatal: err_sep),
                "x.x.xxx.x " => (fatal: err_item),
            );
        }
    }
}
