#![feature(conservative_impl_trait)]

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error<E> {
    Custom(E),
    Whitespace,
    Identifier,
    StrExact(&'static str),
    Either(Box<(Error<E>, Error<E>)>),
    Keyword(&'static str),
    AtLeast(usize, usize),
    EndOfInput,
    CharExact(char),
    CharAny,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Location {
    pub line: usize,
    pub column: usize,
    pub position: usize,
}

impl Location {

    pub fn from_position(input: &str, position: &str) -> Option<Location> {
        if input.ends_with(position) {
            let position = input.len() - position.len();
            let parsed = &input[..position];
            let line_num = 1 + parsed.chars().filter(|c| *c == '\n').count();
            let last_line = match parsed.char_indices().rev().find(|&(_, c)| c == '\n') {
                Some((p, c)) => &parsed[(p + c.len_utf8())..],
                None => parsed,
            };
            let column_num = 1 + last_line.chars().count();
            Some(Location {
                position: position,
                line: line_num,
                column: column_num,
            })
        }
        else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DocumentError<E> {
    pub error: Error<E>,
    pub location: Location,
}

impl<E> DocumentError<E> {

    fn from_input(error: Error<E>, input: &str, position: &str) -> Option<DocumentError<E>> {
        let location = match Location::from_position(input, position) {
            Some(l) => l,
            None => return None,
        };
        Some(DocumentError {
            error: error,
            location: location,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parsed<'a, T> {
    pub value: T,
    pub rest: &'a str,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Failed<'a, E> {
    pub error: Error<E>,
    pub position: &'a str,
}

pub type Result<'a, T, E> = std::result::Result<Parsed<'a, T>, Failed<'a, E>>;

pub fn document<'a, E, V, F>(input: &'a str, parser: F)
-> std::result::Result<V, DocumentError<E>>
where F: Fn(&'a str) -> Result<V, E> {
    match take_left(parser, end_of_input())(input) {
        Ok(Parsed { value, .. }) => Ok(value),
        Err(Failed { error, position })
            => Err(DocumentError::from_input(error, input, position).unwrap()),
    }
}

pub fn position<E>() -> impl Fn(&str) -> Result<&str, E> {
    |input| Ok(Parsed { value: input, rest: input })
}

pub fn nothing<E>() -> impl Fn(&str) -> Result<(), E> {
    |input| Ok(Parsed { value: (), rest: input })
}

pub fn str_until<'a, E, V, F>(end: F) -> impl Fn(&'a str) -> Result<&'a str, E>
where F: Fn(&'a str) -> Result<V, E> {
    move |input| {
        for (p, _) in input.char_indices() {
            if let Ok(Parsed { rest, .. }) = end(&input[p..]) {
                return Ok(Parsed { value: &input[..p], rest: rest });
            }
        }
        Ok(Parsed { value: input, rest: &input[input.len()..] })
    }
}

pub fn error<E, V>(error: E) -> impl Fn(&str) -> Result<V, E>
where E: Clone {
    move |input| Err(Failed { error: Error::Custom(error.clone()), position: input })
}

pub fn error_from<E, V, F>(from: F) -> impl Fn(&str) -> Result<V, E>
where F: Fn() -> E {
    move |input| Err(Failed { error: Error::Custom(from()), position: input })
}

pub fn value<E, V>(value: V) -> impl Fn(&str) -> Result<V, E>
where V: Clone {
    move |input| Ok(Parsed { value: value.clone(), rest: input })
}

pub fn value_from<E, V, F>(from: F) -> impl Fn(&str) -> Result<V, E>
where F: Fn() -> V {
    move |input| Ok(Parsed { value: from(), rest: input })
}

pub fn take_right<'a, E, F1, R1, F2, R2>(left: F1, right: F2)
-> impl Fn(&'a str)
-> Result<R2, E>
    where
        F1: Fn(&'a str) -> Result<R1, E>,
        F2: Fn(&'a str) -> Result<R2, E> {
    move |input| {
        let l_res = left(input)?;
        right(l_res.rest)
    }
}

pub fn take_left<'a, E, F1, R1, F2, R2>(left: F1, right: F2)
-> impl Fn(&'a str)
-> Result<R1, E>
    where
        F1: Fn(&'a str) -> Result<R1, E>,
        F2: Fn(&'a str) -> Result<R2, E> {
    move |input| {
        let l_res = left(input)?;
        let r_res = right(l_res.rest)?;
        Ok(Parsed { value: l_res.value, rest: r_res.rest })
    }
}

pub fn fmap_parsed<'a, E, F, FR, M, MR>(parser: F, mapper: M)
-> impl Fn(&'a str)
-> Result<MR, E>
    where
        F: Fn(&'a str) -> Result<FR, E>,
        M: Fn(FR) -> std::result::Result<MR, E> {
    move |input| {
        match parser(input) {
            Ok(Parsed { value, rest }) => match mapper(value) {
                Ok(value) => Ok(Parsed { value: value, rest: rest }),
                Err(error) => Err(Failed { error: Error::Custom(error), position: input }),
            },
            Err(e) => Err(e),
        }
    }
}

pub fn fmap_failed<'a, E, F, FR, M, ME>(parser: F, mapper: M)
-> impl Fn(&'a str)
-> Result<FR, ME>
    where
        F: Fn(&'a str) -> Result<FR, E>,
        M: Fn(Error<E>) -> std::result::Result<FR, ME> {
    move |input| {
        match parser(input) {
            Ok(v) => Ok(v),
            Err(Failed { error, .. }) => match mapper(error) {
                Ok(value) => Ok(Parsed { value: value, rest: input }),
                Err(error) => Err(Failed { error: Error::Custom(error), position: input }),
            },
        }
    }
}

pub fn map_parsed<'a, E, F, FR, M, MR>(parser: F, mapper: M)
-> impl Fn(&'a str)
-> Result<MR, E>
where F: Fn(&'a str) -> Result<FR, E>, M: Fn(FR) -> MR {
    move |input| {
        match parser(input) {
            Ok(Parsed { value, rest }) => Ok(Parsed { value: mapper(value), rest: rest }),
            Err(e) => Err(e),
        }
    }
}

pub fn map_failed<'a, E, F, FR, M, ME>(parser: F, mapper: M)
-> impl Fn(&'a str)
-> Result<FR, ME>
where F: Fn(&'a str) -> Result<FR, E>, M: Fn(Error<E>) -> ME {
    move |input| {
        match parser(input) {
            Ok(v) => Ok(v),
            Err(Failed { error, position })
                => Err(Failed { error: Error::Custom(mapper(error)), position: position }),
        }
    }
}

pub fn end_of_line<'a, E>() -> impl Fn(&'a str) -> Result<Option<&'a str>, E> {
    either(
        map_parsed(newline(), |s| Some(s)),
        map_parsed(end_of_input(), |_| None),
    )
}

pub fn newline<E>() -> impl Fn(&str) -> Result<&str, E> {
    char_exact('\n')
}

pub fn char_any<E>() -> impl Fn(&str) -> Result<char, E> {
    |input| match input.chars().nth(0) {
        Some(c) => Ok(Parsed { value: c, rest: &input[c.len_utf8()..] }),
        None => Err(Failed { error: Error::CharAny, position: input }),
    }
}

pub fn char_exact<E>(expected: char) -> impl Fn(&str) -> Result<&str, E> {
    move |input| {
        match input.chars().nth(0) {
            Some(c) if c == expected => {
                let len = c.len_utf8();
                Ok(Parsed { value: &input[..len], rest: &input[len..] })
            },
            _ => Err(Failed { error: Error::CharExact(expected), position: input }),
        }
    }
}

pub fn end_of_input<E>() -> impl Fn(&str) -> Result<(), E> {
    |input| {
        if input.len() > 0 {
            Err(Failed { error: Error::EndOfInput, position: input })
        }
        else {
            Ok(Parsed { value: (), rest: input })
        }
    }
}

pub fn list<'a, E, SF, SR, IF, IR, EF, ER>(min: usize, sep: SF, item: IF, end: EF)
-> impl Fn(&'a str)
-> Result<Vec<IR>, E>
    where
        SF: Fn(&'a str) -> Result<SR, E>,
        IF: Fn(&'a str) -> Result<IR, E>,
        EF: Fn(&'a str) -> Result<ER, E> {
    move |input| {
        let mut items = Vec::new();
        let rest =
            if let Ok(Parsed { value, rest }) = item(input) {
                items.push(value);
                let mut current = rest;
                loop {
                    match take_right(&sep, &item)(current) {
                        Ok(Parsed { value, rest }) => {
                            items.push(value);
                            current = rest;
                        },
                        Err(_) => {
                            let Parsed { rest, .. } = end(current)?;
                            current = rest;
                            break;
                        },
                    }
                }
                current
            } else {
                input
            };
        if items.len() >= min {
            Ok(Parsed { value: items, rest: rest })
        }
        else {
            Err(Failed { error: Error::AtLeast(min, items.len()), position: input })
        }
    }
}

pub fn many0<'a, E, F, R>(item: F) -> impl Fn(&'a str) -> Result<Vec<R>, E>
where F: Fn(&'a str) -> Result<R, E> {
    list(0, nothing(), item, nothing())
}

pub fn many1<'a, E, F, R>(item: F) -> impl Fn(&'a str) -> Result<Vec<R>, E>
where F: Fn(&'a str) -> Result<R, E> {
    list(1, nothing(), item, nothing())
}

pub fn any<'a, E, F1, F2, R>(f1: F1, f2: F2) -> impl Fn(&'a str) -> Result<R, E>
where F1: Fn(&'a str) -> Result<R, E>, F2: Fn(&'a str) -> Result<R, E> {
    move |input| {
        if let Ok(v) = f1(input) {
            Ok(v)
        }
        else {
            f2(input)
        }
    }
}

pub fn either<'a, E, F1, F2, R>(f1: F1, f2: F2) -> impl Fn(&'a str) -> Result<R, E>
where F1: Fn(&'a str) -> Result<R, E>, F2: Fn(&'a str) -> Result<R, E> {
    move |input| {
        let err1 = match f1(input) {
            Err(Failed { error, .. }) => error,
            Ok(v) => return Ok(v),
        };
        let err2 = match f2(input) {
            Err(Failed { error, .. }) => error,
            Ok(v) => return Ok(v),
        };
        Err(Failed { error: Error::Either(Box::new((err1, err2))), position: input })
    }
}

pub fn joined0<'a, E, S, SR, I, IR>(sep: S, item: I)
-> impl Fn(&'a str)
-> Result<Vec<IR>, E>
where S: Fn(&'a str) -> Result<SR, E>, I: Fn(&'a str) -> Result<IR, E> {
    list(0, sep, item, nothing())
}

pub fn joined1<'a, E, S, SR, I, IR>(sep: S, item: I)
-> impl Fn(&'a str)
-> Result<Vec<IR>, E>
where S: Fn(&'a str) -> Result<SR, E>, I: Fn(&'a str) -> Result<IR, E> {
    list(1, sep, item, nothing())
}

pub fn separated0<'a, E, S, SR, I, IR>(sep: S, item: I)
-> impl Fn(&'a str)
-> Result<Vec<IR>, E>
where S: Fn(&'a str) -> Result<SR, E>, I: Fn(&'a str) -> Result<IR, E> {
    move |input| list(0, &sep, &item, optional(&sep))(input)
}

pub fn separated1<'a, E, S, SR, I, IR>(sep: S, item: I)
-> impl Fn(&'a str)
-> Result<Vec<IR>, E>
where S: Fn(&'a str) -> Result<SR, E>, I: Fn(&'a str) -> Result<IR, E> {
    move |input| list(1, &sep, &item, optional(&sep))(input)
}

pub fn optional<'a, E, F, R>(parser: F) -> impl Fn(&'a str) -> Result<Option<R>, E>
where F: Fn(&'a str) -> Result<R, E> {
    move |input| {
        match parser(input) {
            Ok(Parsed { value, rest }) => Ok(Parsed { value: Some(value), rest: rest }),
            Err(Failed { .. }) => Ok(Parsed { value: None, rest: input }),
        }
    }
}

pub fn delimited<'a, E, L, LR, R, RR, I, IR>(left: L, center: I, right: R)
-> impl Fn(&'a str)
-> Result<IR, E>
    where
        L: Fn(&'a str) -> Result<LR, E>,
        R: Fn(&'a str) -> Result<RR, E>,
        I: Fn(&'a str) -> Result<IR, E> {
    move |input| {
        let Parsed { rest, .. } = left(input)?;
        let Parsed { value, rest } = center(rest)?;
        let Parsed { rest, .. } = right(rest)?;
        Ok(Parsed { value: value, rest: rest })
    }
}

pub fn combine<'a, E, F1, R1, F2, R2, FR, R>(f1: F1, f2: F2, comb: FR)
-> impl Fn(&'a str)
-> Result<R, E>
    where
        F1: Fn(&'a str) -> Result<R1, E>,
        F2: Fn(&'a str) -> Result<R2, E>,
        FR: Fn(R1, R2) -> R {
    move |input| {
        let Parsed { value: r1, rest } = f1(input)?;
        let Parsed { value: r2, rest } = f2(rest)?;
        Ok(Parsed { value: comb(r1, r2), rest: rest })
    }
}

pub fn str_exact<E>(expected: &'static str) -> impl Fn(&str) -> Result<&str, E> {
    move |input| {
        if input.starts_with(expected) {
            let rest_index = expected.len();
            Ok(Parsed { value: &input[..rest_index], rest: &input[rest_index..] })
        }
        else {
            Err(Failed { error: Error::StrExact(expected), position: input })
        }
    }
}

pub fn keyword<E>(expected: &'static str) -> impl Fn(&str) -> Result<&str, E> {
    move |input| {
        match identifier::<E>()(input) {
            Ok(Parsed { value, rest }) if value == expected
                 => Ok(Parsed { value: value, rest: rest }),
            _ => Err(Failed { error: Error::Keyword(expected), position: input }),
        }
    }
}

pub fn identifier<E>() -> impl Fn(&str) -> Result<&str, E> {
    fn is_identifier_start(c: char) -> bool {
        match c { 'a'...'z' | 'A'...'Z' | '_' => true, _ => false }
    }
    fn is_identifier_tail(c: char) -> bool {
        match c { 'a'...'z' | 'A'...'Z' | '0'...'9' | '_' => true, _ => false }
    }
    |input| {
        let (value, rest) = match input.chars().nth(0) {
            Some(c) if is_identifier_start(c) => input
                .char_indices()
                .find(|&(_, c)| !is_identifier_tail(c))
                .map_or_else(
                    || (input, &input[input.len()..]),
                    |(p, _)| (&input[..p], &input[p..]),
                ),
            _ => return Err(Failed { error: Error::Identifier, position: input }),
        };
        Ok(Parsed { value: value, rest: rest })
    }
}

pub fn whitespace<E>() -> impl Fn(&str) -> Result<&str, E> {
    fn is_whitespace(c: char) -> bool {
        match c { ' ' | '\t' | '\n' => true, _ => false }
    }
    |input| {
        let pos = input.char_indices()
            .find(|&(_, c)| !is_whitespace(c))
            .map_or_else(|| input.len(), |(p, _)| p);
        match pos {
            0 => Err(Failed { error: Error::Whitespace, position: input }),
            p => Ok(Parsed { value: &input[..p], rest: &input[p..] }),
        }
    }
}
