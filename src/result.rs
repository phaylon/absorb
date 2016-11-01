
use ::{ Input, State, Location };

/// The parser result type.
///
/// This type is a `ParseResult` wrapped in a normal `Result`. While `ParseResult`
/// values represent successful or failed parses, the outer error represents a hard
/// error during the parsing operation, like a reached hard-limit.
///
/// In general, parsers will take sub-parser failures into consideration, while hard
/// errors are usually passed up the chain.
pub type PResult<'a, Y, N, E> = Result<ParseResult<'a, Y, N>, E>;

/// Data for a successful parse.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parsed<'a, T> {
    /// The resulting value.
    pub value: T,
    /// The rest of the input after the relevant input has been consumed.
    pub rest: Input<'a>,
    /// The state of the parse result.
    pub state: State,
}

/// Data for a failed parse.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Failed<E> {
    /// The resulting failure value.
    pub error: E,
    /// The location of this error in the input slice.
    pub location: Location,
    /// The state of the parse result.
    pub state: State,
}

/// Result of a parse operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseResult<'a, T, E> {
    /// Contains result of a successful parse.
    Parsed(Parsed<'a, T>),
    /// Contains result of a failed parse.
    Failed(Failed<E>),
}

impl<'a, T, E> ParseResult<'a, T, E> {

    /// Short-hand function for creating a new failed result.
    pub fn new_failed<L>(error: E, state: State, location: L) -> Self
    where L: Into<Location> {
        ParseResult::Failed(Failed { error: error, state: state, location: location.into() })
    }

    /// Short-hand function for creating a new successful result.
    pub fn new_parsed(value: T, state: State, rest: Input<'a>) -> Self {
        ParseResult::Parsed(Parsed { value: value, state: state, rest: rest })
    }

    /// Apply a mapping function if the result represents a failed parse.
    pub fn map_failed<F, X>(self, mapper: F) -> ParseResult<'a, T, X>
    where F: Fn(E) -> X {
        match self {
            ParseResult::Parsed(parsed) => ParseResult::Parsed(parsed),
            ParseResult::Failed(Failed { error, state, location }) =>
                ParseResult::Failed(Failed {
                    error: mapper(error),
                    state: state,
                    location: location,
                }),
        }
    }

    /// Apply a mapping function if the result represents a successful parse.
    pub fn map_parsed<F, U>(self, mapper: F) -> ParseResult<'a, U, E>
    where F: Fn(T) -> U {
        match self {
            ParseResult::Failed(failed) => ParseResult::Failed(failed),
            ParseResult::Parsed(Parsed { value, state, rest }) =>
                ParseResult::Parsed(Parsed {
                    value: mapper(value),
                    state: state,
                    rest: rest,
                }),
        }
    }

    /// Return a new `ParseResult` with the passed in state merged in.
    ///
    /// See `State::merge` for more information.
    pub fn merge_state(self, new_state: State) -> Self {
        match self {
            ParseResult::Parsed(Parsed { value, state, rest }) =>
                ParseResult::Parsed(Parsed {
                    value: value,
                    state: state.merge(new_state),
                    rest: rest,
                }),
            ParseResult::Failed(Failed { error, state, location }) =>
                ParseResult::Failed(Failed {
                    error: error,
                    state: state.merge(new_state),
                    location: location,
                }),
        }
    }
}
