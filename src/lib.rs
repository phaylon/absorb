#![feature(conservative_impl_trait)]

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error<E> {
    Custom(E),
    StrWhitespace,
    StrIdentifier,
    StrExact(&'static str),
    StrKeyword(&'static str),
    CharExact(char),
    CharAny,
    ListEnd,
    Either(Box<(Error<E>, Error<E>)>),
    AtLeast(usize, usize),
    EndOfInput,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Input<'a> {
    slice: &'a str,
    location: Location,
}

impl<'a> Input<'a> {

    pub fn slice(&self) -> &'a str { self.slice }

    pub fn len(&self) -> usize { self.slice.len() }

    pub fn is_empty(&self) -> bool { self.slice.len() == 0 }

    pub fn location(&self) -> Location { self.location }

    pub fn consume_all(&self) -> (&'a str, Input<'a>) {
        self.consume(self.len())
    }

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

pub fn parse<'a, V, E, P>(input_str: &'a str, parser: P)
-> std::result::Result<(V, State, &'a str), (Error<E>, State, Location)>
where P: Fn(Input<'a>) -> Result<V, E> {
    let input = Input {
        slice: input_str,
        location: Location {
            position: 0,
            line: 1,
            column: 1,
        }
    };
    match parser(input) {
        Ok(Parsed { value, rest, state }) => Ok((value, state, rest.slice())),
        Err(Failed { error, location, state }) => Err((error, state, location)),
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Location {
    pub line: usize,
    pub column: usize,
    pub position: usize,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum State {
    Complete,
    Incomplete,
}

impl State {

    pub fn merge(self, other: State) -> State {
        match (self, other) {
            (State::Complete, State::Complete) => State::Complete,
            _ => State::Incomplete,
        }
    }

    pub fn merge_into<V, E>(self, result: Result<V, E>) -> Result<V, E> {
        match result {
            Ok(Parsed { value, rest, state })
                => Ok(Parsed { value: value, rest: rest, state: self.merge(state) }),
            Err(Failed { error, location, state })
                => Err(Failed { error: error, location: location, state: self.merge(state) }),
        }
    }

    fn from_expected_input(input: Input, expected: &str) -> State {
        if input.len() >= expected.len() { State::Complete }
        else if expected.starts_with(input.slice()) { State::Incomplete }
        else { State::Complete }
    }

    fn from_rest(input: Input) -> State {
        if !input.is_empty() { State::Complete }
        else { State::Incomplete }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parsed<'a, T> {
    pub value: T,
    pub rest: Input<'a>,
    pub state: State,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Failed<E> {
    pub error: Error<E>,
    pub location: Location,
    pub state: State,
}

pub type Result<'a, T, E> = std::result::Result<Parsed<'a, T>, Failed<E>>;

pub fn document<'a, E, V, F>(input: &'a str, parser: F)
-> std::result::Result<V, (Error<E>, Location)>
where F: Fn(Input<'a>) -> Result<V, E> {
    match parse(input, complete(take_left(parser, end_of_input()))) {
        Ok((value, _, _)) => Ok(value),
        Err((error, _, location)) => Err((error, location)),
    }
}

pub fn complete<'a, E, V, F>(parser: F) -> impl Fn(Input<'a>) -> Result<V, E>
where F: Fn(Input<'a>) -> Result<V, E> {
    move |input| match parser(input) {
        Ok(Parsed { value, rest, .. })
            => Ok(Parsed { value: value, rest: rest, state: State::Complete }),
        Err(Failed { error, location, .. })
            => Err(Failed { error: error, location: location, state: State::Complete }),
    }
}

pub fn location<E>() -> impl Fn(Input) -> Result<Location, E> {
    |input| Ok(Parsed { value: input.location(), rest: input, state: State::Complete })
}

pub fn str_until<'a, E, V, F>(end: F) -> impl Fn(Input<'a>) -> Result<&'a str, E>
where F: Fn(Input<'a>) -> Result<V, E> {
    move |input| {
        let mut current = input;
        let mut consumed = 0;
        loop {
            match end(current) {
                Ok(Parsed { rest, state, .. }) => {
                    let (span, input_rest) = input.consume(consumed);
                    return Ok(Parsed {
                        value: span,
                        rest: rest,
                        state: State::from_rest(input_rest).merge(state),
                    });
                },
                Err(failed) => match current.slice().chars().nth(0) {
                    Some(c) => {
                        let (_, new) = current.consume(c.len_utf8());
                        current = new;
                        consumed += c.len_utf8();
                    },
                    None => return Err(failed),
                },
            }
        }
    }
}

pub fn char_any<E>() -> impl Fn(Input) -> Result<char, E> {
    |input| match input.slice().chars().nth(0) {
        Some(c) => {
            let (_, rest) = input.consume(c.len_utf8());
            Ok(Parsed { value: c, rest: rest, state: State::Complete })
        },
        None => Err(Failed {
            error: Error::CharAny,
            location: input.location(),
            state: State::Incomplete,
        }),
    }
}

pub fn value_from<E, V, F>(from: F) -> impl Fn(Input) -> Result<V, E>
where F: Fn() -> V {
    move |input| Ok(Parsed { value: from(), rest: input, state: State::Complete })
}

pub fn value<E, V>(value: V) -> impl Fn(Input) -> Result<V, E>
where V: Clone {
    move |input| Ok(Parsed { value: value.clone(), rest: input, state: State::Complete })
}

pub fn take_left<'a, E, F1, R1, F2, R2>(left: F1, right: F2)
-> impl Fn(Input<'a>)
-> Result<R1, E>
    where
        F1: Fn(Input<'a>) -> Result<R1, E>,
        F2: Fn(Input<'a>) -> Result<R2, E> {
    move |input| {
        let l_res = left(input)?;
        let r_res = right(l_res.rest)?;
        Ok(Parsed {
            value: l_res.value,
            rest: r_res.rest,
            state: l_res.state.merge(r_res.state),
        })
    }
}

pub fn error_fmap<'a, E, F, FR, M, ME>(parser: F, mapper: M)
-> impl Fn(Input<'a>)
-> Result<FR, ME>
    where
        F: Fn(Input<'a>) -> Result<FR, E>,
        M: Fn(Error<E>) -> std::result::Result<FR, ME> {
    move |input| {
        match parser(input) {
            Ok(v) => Ok(v),
            Err(Failed { error, state, location }) => match mapper(error) {
                Ok(value) => Ok(Parsed { value: value, rest: input, state: state }),
                Err(error) => Err(Failed {
                    error: Error::Custom(error),
                    location: location,
                    state: state,
                }),
            },
        }
    }
}

pub fn error_map<'a, E, F, FR, M, ME>(parser: F, mapper: M)
-> impl Fn(Input<'a>)
-> Result<FR, ME>
where F: Fn(Input<'a>) -> Result<FR, E>, M: Fn(Error<E>) -> ME {
    move |input| {
        match parser(input) {
            Ok(v) => Ok(v),
            Err(Failed { error, location, state }) => Err(Failed {
                error: Error::Custom(mapper(error)),
                location: location,
                state: state,
            }),
        }
    }
}

pub fn value_fmap<'a, E, F, FR, M, MR>(parser: F, mapper: M)
-> impl Fn(Input<'a>)
-> Result<MR, E>
    where
        F: Fn(Input<'a>) -> Result<FR, E>,
        M: Fn(FR) -> std::result::Result<MR, E> {
    move |input| {
        match parser(input) {
            Ok(Parsed { value, rest, state }) => match mapper(value) {
                Ok(value) => Ok(Parsed { value: value, rest: rest, state: state }),
                Err(error) => Err(Failed {
                    error: Error::Custom(error),
                    location: input.location(),
                    state: state,
                }),
            },
            Err(e) => Err(e),
        }
    }
}

pub fn end_of_line<'a, E>() -> impl Fn(Input<'a>) -> Result<Option<char>, E> {
    either(
        value_map(end_of_input(), |_| None),
        value_map(char_newline(), |s| Some(s)),
    )
}

pub fn value_map<'a, E, F, FR, M, MR>(parser: F, mapper: M)
-> impl Fn(Input<'a>)
-> Result<MR, E>
where F: Fn(Input<'a>) -> Result<FR, E>, M: Fn(FR) -> MR {
    move |input| {
        match parser(input) {
            Ok(Parsed { value, rest, state }) => Ok(Parsed {
                value: mapper(value),
                rest: rest,
                state: state,
            }),
            Err(e) => Err(e),
        }
    }
}

pub fn char_newline<E>() -> impl Fn(Input) -> Result<char, E> {
    char_exact('\n')
}

pub fn end_of_input<E>() -> impl Fn(Input) -> Result<(), E> {
    |input| {
        if !input.is_empty() {
            Err(Failed {
                error: Error::EndOfInput,
                location: input.location(),
                state: State::Complete,
            })
        }
        else {
            Ok(Parsed { value: (), rest: input, state: State::Incomplete })
        }
    }
}

pub fn error_from<E, V, F>(state: State, from: F) -> impl Fn(Input) -> Result<V, E>
where F: Fn() -> E {
    move |input| Err(Failed {
        error: Error::Custom(from()),
        location: input.location(),
        state: state,
    })
}

pub fn error<E, V>(state: State, error: E) -> impl Fn(Input) -> Result<V, E>
where E: Clone {
    move |input| Err(Failed {
        error: Error::Custom(error.clone()),
        location: input.location(),
        state: state,
    })
}

pub fn any<'a, E, F1, F2, R>(f1: F1, f2: F2) -> impl Fn(Input<'a>) -> Result<R, E>
where F1: Fn(Input<'a>) -> Result<R, E>, F2: Fn(Input<'a>) -> Result<R, E> {
    move |input| {
        match f1(input) {
            Ok(v) => Ok(v),
            Err(Failed { state, .. }) => state.merge_into(f2(input)),
        }
    }
}

pub fn many0<'a, E, F, R>(item: F) -> impl Fn(Input<'a>) -> Result<Vec<R>, E>
where F: Fn(Input<'a>) -> Result<R, E> {
    list(0, nothing(), item, nothing())
}

pub fn many1<'a, E, F, R>(item: F) -> impl Fn(Input<'a>) -> Result<Vec<R>, E>
where F: Fn(Input<'a>) -> Result<R, E> {
    list(1, nothing(), item, nothing())
}

pub fn either<'a, E, F1, F2, R>(f1: F1, f2: F2)
-> impl Fn(Input<'a>)
-> Result<R, E>
where F1: Fn(Input<'a>) -> Result<R, E>, F2: Fn(Input<'a>) -> Result<R, E> {
    move |input| {
        let (err1, state1) = match f1(input) {
            Err(Failed { error, state, .. }) => (error, state),
            Ok(v) => return Ok(v),
        };
        let (err2, state2) = match f2(input) {
            Err(Failed { error, state, .. }) => (error, state),
            Ok(v) => return state1.merge_into(Ok(v)),
        };
        Err(Failed {
            error: Error::Either(Box::new((err1, err2))),
            location: input.location(),
            state: state1.merge(state2),
        })
    }
}

pub fn separated0<'a, E, S, SR, I, IR>(sep: S, item: I)
-> impl Fn(Input<'a>)
-> Result<Vec<IR>, E>
where S: Fn(Input<'a>) -> Result<SR, E>, I: Fn(Input<'a>) -> Result<IR, E> {
    move |input| list(0, &sep, &item, optional(&sep))(input)
}

pub fn separated1<'a, E, S, SR, I, IR>(sep: S, item: I)
-> impl Fn(Input<'a>)
-> Result<Vec<IR>, E>
where S: Fn(Input<'a>) -> Result<SR, E>, I: Fn(Input<'a>) -> Result<IR, E> {
    move |input| list(1, &sep, &item, optional(&sep))(input)
}

pub fn joined0<'a, E, S, SR, I, IR>(sep: S, item: I)
-> impl Fn(Input<'a>)
-> Result<Vec<IR>, E>
where S: Fn(Input<'a>) -> Result<SR, E>, I: Fn(Input<'a>) -> Result<IR, E> {
    list(0, sep, item, nothing())
}

pub fn joined1<'a, E, S, SR, I, IR>(sep: S, item: I)
-> impl Fn(Input<'a>)
-> Result<Vec<IR>, E>
where S: Fn(Input<'a>) -> Result<SR, E>, I: Fn(Input<'a>) -> Result<IR, E> {
    list(1, sep, item, nothing())
}

pub fn nothing<E>() -> impl Fn(Input) -> Result<(), E> {
    |input| Ok(Parsed { value: (), rest: input, state: State::Complete })
}

pub fn char_exact<E>(expected: char) -> impl Fn(Input) -> Result<char, E> {
    move |input| {
        match input.slice().chars().nth(0) {
            Some(c) if c == expected => {
                let (_, rest) = input.consume(c.len_utf8());
                Ok(Parsed { value: c, rest: rest, state: State::Complete })
            },
            _ => Err(Failed {
                error: Error::CharExact(expected),
                location: input.location(),
                state: State::from_rest(input),
            }),
        }
    }
}

pub fn take_right<'a, E, F1, R1, F2, R2>(left: F1, right: F2)
-> impl Fn(Input<'a>)
-> Result<R2, E>
    where
        F1: Fn(Input<'a>) -> Result<R1, E>,
        F2: Fn(Input<'a>) -> Result<R2, E> {
    move |input| {
        let l_res = left(input)?;
        l_res.state.merge_into(right(l_res.rest))
    }
}

pub fn list<'a, E, SF, SR, IF, IR, EF, ER>(min: usize, sep: SF, item: IF, end: EF)
-> impl Fn(Input<'a>)
-> Result<Vec<IR>, E>
    where
        SF: Fn(Input<'a>) -> Result<SR, E>,
        IF: Fn(Input<'a>) -> Result<IR, E>,
        EF: Fn(Input<'a>) -> Result<ER, E> {
    move |input| {
        let mut items = Vec::new();
        let mut all_state = State::Complete;
        let rest = match item(input) {
            Ok(Parsed { value, rest, state }) => {
                items.push(value);
                all_state = all_state.merge(state);
                let mut current = rest;
                loop {
                    match take_right(&sep, &item)(current) {
                        Ok(Parsed { value, rest, state }) => {
                            items.push(value);
                            current = rest;
                            all_state = all_state.merge(state);
                        },
                        Err(Failed { state, .. }) => {
                            all_state = all_state.merge(state);
                            let Parsed { rest, state: end_state, .. } = match end(current) {
                                Ok(parsed) => parsed,
                                Err(failed) => {
                                    all_state = all_state.merge(failed.state);
                                    return Err(Failed {
                                        error: Error::ListEnd,
                                        location: current.location(),
                                        state: all_state,
                                    });
                                },
                            };
                            current = rest;
                            all_state = all_state.merge(end_state);
                            break;
                        },
                    }
                }
                current
            },
            Err(Failed { state, .. }) => {
                all_state = all_state.merge(state);
                input
            },
        };
        if items.len() >= min {
            Ok(Parsed {
                value: items,
                rest: rest,
                state: all_state.merge(State::from_rest(rest)),
            })
        }
        else {
            Err(Failed {
                error: Error::AtLeast(min, items.len()),
                location: input.location(),
                state: all_state.merge(State::from_rest(rest)),
            })
        }
    }
}

pub fn optional<'a, E, F, R>(parser: F)
-> impl Fn(Input<'a>)
-> Result<Option<R>, E>
where F: Fn(Input<'a>) -> Result<R, E> {
    move |input| {
        match parser(input) {
            Ok(Parsed { value, rest, state }) => Ok(Parsed {
                value: Some(value),
                rest: rest,
                state: state,
            }),
            Err(Failed { state, .. }) => Ok(Parsed { value: None, rest: input, state: state }),
        }
    }
}

pub fn delimited<'a, E, L, LR, R, RR, I, IR>(left: L, center: I, right: R)
-> impl Fn(Input<'a>)
-> Result<IR, E>
    where
        L: Fn(Input<'a>) -> Result<LR, E>,
        R: Fn(Input<'a>) -> Result<RR, E>,
        I: Fn(Input<'a>) -> Result<IR, E> {
    move |input| {
        let Parsed { state: state_l, rest, .. } = left(input)?;
        let Parsed { state: state_c, value, rest } = center(rest)?;
        let Parsed { state: state_r, rest, .. } = right(rest)?;
        Ok(Parsed {
            value: value,
            rest: rest,
            state: state_l.merge(state_c).merge(state_r),
        })
    }
}

pub fn combine<'a, E, F1, R1, F2, R2, FR, R>(f1: F1, f2: F2, comb: FR)
-> impl Fn(Input<'a>)
-> Result<R, E>
    where
        F1: Fn(Input<'a>) -> Result<R1, E>,
        F2: Fn(Input<'a>) -> Result<R2, E>,
        FR: Fn(R1, R2) -> R {
    move |input| {
        let Parsed { state: state1, value: r1, rest } = f1(input)?;
        let Parsed { state: state2, value: r2, rest } = f2(rest)?;
        Ok(Parsed { value: comb(r1, r2), rest: rest, state: state1.merge(state2) })
    }
}

pub fn str_exact<E>(expected: &'static str) -> impl Fn(Input) -> Result<&str, E> {
    move |input| {
        if input.slice().starts_with(expected) {
            let (value, rest) = input.consume(expected.len());
            Ok(Parsed {
                value: value,
                rest: rest,
                state: State::Complete,
            })
        }
        else {
            Err(Failed {
                error: Error::StrExact(expected),
                location: input.location(),
                state: State::from_expected_input(input, expected),
            })
        }
    }
}

pub fn str_keyword<E>(expected: &'static str) -> impl Fn(Input) -> Result<&str, E> {
    move |input| {
        match str_identifier::<E>()(input) {
            Ok(Parsed { value, rest, state }) if value == expected
                 => Ok(Parsed { value: value, rest: rest, state: state }),
            Ok(_) => Err(Failed {
                error: Error::StrKeyword(expected),
                location: input.location(),
                state: State::from_expected_input(input, expected),
            }),
            Err(Failed { state, .. }) => Err(Failed {
                error: Error::StrKeyword(expected),
                location: input.location(),
                state: State::from_expected_input(input, expected).merge(state),
            }),
        }
    }
}

pub fn str_identifier<E>() -> impl Fn(Input) -> Result<&str, E> {
    fn is_identifier_start(c: char) -> bool {
        match c { 'a'...'z' | 'A'...'Z' | '_' => true, _ => false }
    }
    fn is_identifier_tail(c: char) -> bool {
        match c { 'a'...'z' | 'A'...'Z' | '0'...'9' | '_' => true, _ => false }
    }
    |input| {
        let (value, rest) = match input.slice().chars().nth(0) {
            Some(c) if is_identifier_start(c) => input
                .slice()
                .char_indices()
                .find(|&(_, c)| !is_identifier_tail(c))
                .map_or_else(
                    || input.consume_all(),
                    |(p, _)| input.consume(p),
                ),
            _ => return Err(Failed {
                error: Error::StrIdentifier,
                location: input.location(),
                state: State::from_rest(input),
            }),
        };
        Ok(Parsed {
            value: value,
            rest: rest,
            state: State::from_rest(rest),
        })
    }
}

pub fn str_whitespace<E>() -> impl Fn(Input) -> Result<&str, E> {
    fn is_whitespace(c: char) -> bool {
        match c { ' ' | '\t' | '\n' => true, _ => false }
    }
    |input| {
        let pos = input.slice().char_indices()
            .find(|&(_, c)| !is_whitespace(c))
            .map_or_else(|| input.len(), |(p, _)| p);
        match pos {
            0 => Err(Failed {
                error: Error::StrWhitespace,
                location: input.location(),
                state: State::from_rest(input),
            }),
            p => {
                let (slice, rest) = input.consume(p);
                Ok(Parsed {
                    value: slice,
                    rest: rest,
                    state: State::from_rest(rest),
                })
            },
        }
    }
}


