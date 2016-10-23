
extern crate parsoid;
use parsoid as par;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum TestError {
    Test,
}

#[derive( Debug, Clone, PartialEq, Eq )]
struct Wrap<T>(T);

macro_rules! test {
    ($name:ident($($arg:tt)*): $( $input:expr => ($($check:tt)*) ),* $(,)*) => {
        test!($name($($arg)*) -> _: $( $input => ($($check)*) ),*)
    };
    ($name:ident($($arg:tt)*) -> $ret:ty: $( $input:expr => ($($check:tt)*) ),* $(,)*) => {
        {
            let parser = {
                use parsoid::*;
                |input| {
                    let result: parsoid::Result<$ret, TestError> = $name($($arg)*)(input);
                    result
                }
            };
            let desc = stringify!($name($($arg)*));
            $(
            test_case!(&parser, desc, $input, ($($check)*));
            )*
        }
    }
}

macro_rules! test_case {
    ($parser:expr, $parser_desc:expr, $input:expr, ($($check:tt)*)) => {
        {
            let result = parsoid::parse::<_, TestError, _>($input, $parser);
            test_case_check!($parser_desc, $input, result, $($check)*);
        }
    }
}

macro_rules! test_case_check {
    ($parser_desc:expr, $input:expr, $result:expr, ok: $value:expr, $loc:expr) => {
        test_case_ok!(
            $parser_desc, $input, $result, $value, parsoid::State::Complete, $loc
        );
    };
    ($parser_desc:expr, $input:expr, $result:expr, ok?: $value:expr, $loc:expr) => {
        test_case_ok!(
            $parser_desc, $input, $result, $value, parsoid::State::Incomplete, $loc
        );
    };
    ($parser_desc:expr, $input:expr, $result:expr, err: $error:expr, $loc:expr) => {
        test_case_err!(
            $parser_desc, $input, $result, $error, parsoid::State::Complete, $loc
        );
    };
    ($parser_desc:expr, $input:expr, $result:expr, err?: $error:expr, $loc:expr) => {
        test_case_err!(
            $parser_desc, $input, $result, $error, parsoid::State::Incomplete, $loc
        );
    }
}

macro_rules! test_case_err {
    ($parser_desc:expr,
        $input:expr, $result:expr, $error:expr, $state:expr, $loc:expr
    ) => {
        {
            let (error, state, loc) = match $result {
                Err((e, s, l)) => (e, s, l),
                Ok((v, s, r)) => panic!(
                    "{} <- {:?}:\n\tExpected an Err result but received {}\n",
                    $parser_desc, $input,
                    format!("Ok value {:?} (state {:?}) with rest {:?}", v, s, r)
                ),
            };
            let expected = { #[allow(unused_imports)] use parsoid::*; $error };
            assert!(&error == &expected,
                "{} -> {:?}:\n\t! Error is not as expected.\n\t\
                    Expected: {:?}\n\tReceived: {:?}\n",
                $parser_desc, $input,
                expected, error
            );
            assert!(state == $state,
                "{} -> {:?}:\n\t! State is not as expected.\n\t\
                    Expected: {:?}\n\tReceived: {:?}\n",
                $parser_desc, $input,
                $state, state
            );
            let expected_loc = par::Location { position: $loc.0, line: $loc.1, column: $loc.2 };
            assert!(loc == expected_loc,
                "{} -> {:?}:\n\t! Error location is not as expected.\n\t\
                    Expected: {:?}\n\tReceived: {:?}\n",
                $parser_desc, $input,
                expected_loc, loc
            );
        }
    }
}

macro_rules! test_case_ok {
    ($parser_desc:expr,
        $input:expr, $result:expr, $value:expr, $state:expr, $loc:expr
    ) => {
        {
            let (value, state, rest) = match $result {
                Ok((v, s, r)) => (v, s, r),
                Err((e, s, l)) => panic!(
                    "{} <- {:?}:\n\tExpected an Ok result) but received {}\n",
                    $parser_desc, $input,
                    format!("error '{:?}' (state {:?}) at {:?}", e, s, l)
                ),
            };
            let expected = $value;
            assert!(&value == &expected,
                "{} -> {:?}:\n\t! Value is not as expected.\n\t\
                    Expected: {:?}\n\tReceived: {:?}\n",
                $parser_desc, $input,
                expected, value
            );
            assert!(state == $state,
                "{} -> {:?}:\n\t! State is not as expected.\n\t\
                    Expected: {:?}\n\tReceived: {:?}\n",
                $parser_desc, $input,
                $state, state
            );
            assert!(rest == $loc,
                "{} -> {:?}:\n\t! Leftover content is not as expected.\n\t\
                    Expected: {:?}\n\tReceived: {:?}\n",
                $parser_desc, $input,
                $loc, rest
            );
        }
    }
}

#[test]
fn test_infer() {
    let _ = str_identifier();
}

#[test]
fn document() {
    let loc = |p, l, c| par::Location { position: p, line: l, column: c };
    let doc = |input| par::document::<(), _, _>(input, par::many0(par::char_exact('x')));
    assert_eq!(doc("xxx"), Ok(vec!['x', 'x', 'x']));
    assert_eq!(doc("xxy"), Err((par::Error::EndOfInput, loc(2, 1, 3))));
}

#[test]
fn complete() {
    test!(complete(str_identifier()):
        "" => (err: Error::StrIdentifier, (0, 1, 1)),
        " " => (err: Error::StrIdentifier, (0, 1, 1)),
        "foo" => (ok: "foo", ""),
        "foo " => (ok: "foo", " "),
    );
}

#[test]
fn location() {
    let loc = |p, l, c| par::Location { position: p, line: l, column: c };
    test!(take_right(optional(str_whitespace()), take_right(str_identifier(), location())):
        "foo." => (ok: loc(3, 1, 4), "."),
        "    foo." => (ok: loc(7, 1, 8), "."),
        "  \n\t  \n  foo." => (ok: loc(12, 3, 6), "."),
    );
}

#[test]
fn str_until() {
    test!(str_until(char_newline()):
        "foo\nbar\nbaz" => (ok: "foo", "bar\nbaz"),
        "foo\n " => (ok: "foo", " "),
        "f\n " => (ok: "f", " "),
        "\n " => (ok: "", " "),
        "" => (err?: Error::CharExact('\n'), (0, 1, 1)),
        "foo" => (err?: Error::CharExact('\n'), (3, 1, 4)),
    );
    test!(str_until(str_identifier()):
        "  foo" => (ok?: "  ", ""),
        "  foo " => (ok: "  ", " "),
        "  " => (err?: Error::StrIdentifier, (2, 1, 3)),
    );
}

#[test]
fn char_any() {
    test!(char_any():
        "foo" => (ok: 'f', "oo"),
        "f" => (ok: 'f', ""),
        "\t" => (ok: '\t', ""),
        "" => (err?: Error::CharAny, (0, 1, 1)),
    );
}

#[test]
fn value_from() {
    test!(value_from(|| 23):
        "" => (ok: 23, ""),
        " " => (ok: 23, " "),
    );
    test!(either(str_identifier(), value_from(|| "new")):
        "foo" => (ok?: "foo", ""),
        "foo " => (ok: "foo", " "),
        "" => (ok?: "new", ""),
        " " => (ok: "new", " "),
    );
}

#[test]
fn value() {
    test!(value(23):
        "" => (ok: 23, ""),
        " " => (ok: 23, " "),
    );
    test!(either(str_identifier(), value("new")):
        "foo" => (ok?: "foo", ""),
        "foo " => (ok: "foo", " "),
        "" => (ok?: "new", ""),
        " " => (ok: "new", " "),
    );
}

#[test]
fn take_left() {
    test!(take_left(str_exact("foo"), str_exact("bar")):
        "foobar" => (ok: "foo", ""),
        "foobarbaz" => (ok: "foo", "baz"),
        "foob" => (err?: Error::StrExact("bar"), (3, 1, 4)),
        "foo" => (err?: Error::StrExact("bar"), (3, 1, 4)),
        "foobyr" => (err: Error::StrExact("bar"), (3, 1, 4)),
        "f" => (err?: Error::StrExact("foo"), (0, 1, 1)),
        "" => (err?: Error::StrExact("foo"), (0, 1, 1)),
        "fyybar" => (err: Error::StrExact("foo"), (0, 1, 1)),
    );
}

#[test]
fn error_fmap() {
    test!(
        error_fmap(str_identifier::<()>(), |e| {
            assert_eq!(e, Error::StrIdentifier);
            Ok("new")
        }):
        "foo" => (ok?: "foo", ""),
        "foo " => (ok: "foo", " "),
        "" => (ok?: "new", ""),
        "23" => (ok: "new", "23"),
    );
    test!(
        error_fmap(str_identifier::<()>(), |e| {
            assert_eq!(e, Error::StrIdentifier);
            Err(TestError::Test)
        }):
        "foo" => (ok?: "foo", ""),
        "foo " => (ok: "foo", " "),
        "" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
        "23" => (err: Error::Custom(TestError::Test), (0, 1, 1)),
    );
}

#[test]
fn error_map() {
    test!(
        error_map(str_identifier::<()>(), |e| {
            assert_eq!(e, Error::StrIdentifier);
            TestError::Test
        }):
        "foo" => (ok?: "foo", ""),
        "foo " => (ok: "foo", " "),
        "" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
        "23" => (err: Error::Custom(TestError::Test), (0, 1, 1)),
    );
}

#[test]
fn value_fmap() {
    test!(value_fmap(str_identifier(), |v| Ok(Wrap(v))):
        "foo" => (ok?: Wrap("foo"), ""),
        "foo " => (ok: Wrap("foo"), " "),
        "" => (err?: Error::StrIdentifier, (0, 1, 1)),
        "23" => (err: Error::StrIdentifier, (0, 1, 1)),
    );
    test!(value_fmap(str_identifier(), |_| Err(TestError::Test)) -> ():
        "foo" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
        "foo " => (err: Error::Custom(TestError::Test), (0, 1, 1)),
        "" => (err?: Error::StrIdentifier, (0, 1, 1)),
        "23" => (err: Error::StrIdentifier, (0, 1, 1)),
    );
}

#[test]
fn end_of_line() {
    test!(end_of_line():
        "" => (ok?: None, ""),
        "\n" => (ok: Some('\n'), ""),
        "\n " => (ok: Some('\n'), " "),
        " " => (err: Error::Either(Box::new((
            Error::EndOfInput,
            Error::CharExact('\n'),
        ))), (0, 1, 1)),
    );
}

#[test]
fn value_map() {
    test!(value_map(str_identifier(), |v| Wrap(v)):
        "foo" => (ok?: Wrap("foo"), ""),
        "foo " => (ok: Wrap("foo"), " "),
        "" => (err?: Error::StrIdentifier, (0, 1, 1)),
        "23" => (err: Error::StrIdentifier, (0, 1, 1)),
    );
}

#[test]
fn char_newline() {
    test!(char_newline():
        "\n\n " => (ok: '\n', "\n "),
        "\n" => (ok: '\n', ""),
        "\t" => (err: Error::CharExact('\n'), (0, 1, 1)),
        "" => (err?: Error::CharExact('\n'), (0, 1, 1)),
    );
}

#[test]
fn end_of_input() {
    test!(end_of_input():
        "" => (ok?: (), ""),
        " " => (err: Error::EndOfInput, (0, 1, 1)),
        "\n" => (err: Error::EndOfInput, (0, 1, 1)),
    );
}

#[test]
fn error_from() {
    test!(error_from(State::Complete, || TestError::Test) -> ():
        "" => (err: Error::Custom(TestError::Test), (0, 1, 1)),
        "23" => (err: Error::Custom(TestError::Test), (0, 1, 1)),
    );
    test!(error_from(State::Incomplete, || TestError::Test) -> ():
        "" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
        "23" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
    );
    test!(any(str_exact("foo"), error_from(State::Complete, || TestError::Test)):
        "foo" => (ok: "foo", ""),
        "bar" => (err: Error::Custom(TestError::Test), (0, 1, 1)),
        "fo" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
        "" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
    );
    test!(any(str_exact("foo"), error_from(State::Incomplete, || TestError::Test)):
        "foo" => (ok: "foo", ""),
        "bar" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
        "fo" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
        "" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
    );
}

#[test]
fn error() {
    test!(error(State::Complete, TestError::Test) -> ():
        "" => (err: Error::Custom(TestError::Test), (0, 1, 1)),
        "23" => (err: Error::Custom(TestError::Test), (0, 1, 1)),
    );
    test!(error(State::Incomplete, TestError::Test) -> ():
        "" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
        "23" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
    );
    test!(any(str_exact("foo"), error(State::Complete, TestError::Test)):
        "foo" => (ok: "foo", ""),
        "bar" => (err: Error::Custom(TestError::Test), (0, 1, 1)),
        "fo" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
        "" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
    );
    test!(any(str_exact("foo"), error(State::Incomplete, TestError::Test)):
        "foo" => (ok: "foo", ""),
        "bar" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
        "fo" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
        "" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
    );
}

#[test]
fn any() {
    test!(any(any(str_exact("foo"), str_exact("bar")), error(State::Complete, TestError::Test)):
        "foo" => (ok: "foo", ""),
        "bar" => (ok: "bar", ""),
        "fo" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
        "ba" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
        "" => (err?: Error::Custom(TestError::Test), (0, 1, 1)),
        "qux" => (err: Error::Custom(TestError::Test), (0, 1, 1)),
    );
}

#[test]
fn many0() {
    test!(many0(str_exact("foo")):
        "foo" => (ok?: vec!["foo"], ""),
        "foo23" => (ok: vec!["foo"], "23"),
        "foofoo" => (ok?: vec!["foo", "foo"], ""),
        "fo" => (ok?: Vec::<&str>::new(), "fo"),
        "foofo" => (ok?: vec!["foo"], "fo"),
        "23" => (ok: Vec::<&str>::new(), "23"),
        "" => (ok?: Vec::<&str>::new(), ""),
    );
}

#[test]
fn many1() {
    test!(many1(str_exact("foo")):
        "foo" => (ok?: vec!["foo"], ""),
        "foo23" => (ok: vec!["foo"], "23"),
        "foofoo" => (ok?: vec!["foo", "foo"], ""),
        "fo" => (err?: Error::AtLeast(1, 0), (0, 1, 1)),
        "foofo" => (ok?: vec!["foo"], "fo"),
        "23" => (err: Error::AtLeast(1, 0), (0, 1, 1)),
        "" => (err?: Error::AtLeast(1, 0), (0, 1, 1)),
    );
}

#[test]
fn either() {
    let make_error = || par::Error::Either(Box::new((
        par::Error::StrExact("foo"),
        par::Error::StrExact("bar"),
    )));
    test!(either(str_exact("foo"), str_exact("bar")):
        "foo" => (ok: "foo", ""),
        "foo " => (ok: "foo", " "),
        "foobar" => (ok: "foo", "bar"),
        "bar" => (ok: "bar", ""),
        "baz" => (err: make_error(), (0, 1, 1)),
        "f" => (err?: make_error(), (0, 1, 1)),
        "ba" => (err?: make_error(), (0, 1, 1)),
        "" => (err?: make_error(), (0, 1, 1)),
    );
    test!(either(str_identifier(), str_exact("")):
        "foo" => (ok?: "foo", ""),
        "foo " => (ok: "foo", " "),
        "" => (ok?: "", ""),
    );
}

#[test]
fn separated0() {
    test!(separated0(char_exact(','), str_identifier()):
        "a" => (ok?: vec!["a"], ""),
        "a,b,c" => (ok?: vec!["a", "b", "c"], ""),
        "a,b,c 23" => (ok: vec!["a", "b", "c"], " 23"),
        "23" => (ok: Vec::<&str>::new(), "23"),
        "" => (ok?: Vec::<&str>::new(), ""),
        "a,b,,c" => (ok: vec!["a", "b"], ",c"),
    );
}

#[test]
fn separated1() {
    test!(separated1(char_exact(','), str_identifier()):
        "a" => (ok?: vec!["a"], ""),
        "a,b,c" => (ok?: vec!["a", "b", "c"], ""),
        "a,b,c 23" => (ok: vec!["a", "b", "c"], " 23"),
        "23" => (err: Error::AtLeast(1, 0), (0, 1, 1)),
        "" => (err?: Error::AtLeast(1, 0), (0, 1, 1)),
        "a,b,,c" => (ok: vec!["a", "b"], ",c"),
    );
}

#[test]
fn test_joined0() {
    test!(joined0(char_exact(','), str_identifier()):
        "a" => (ok?: vec!["a"], ""),
        "a,b,c" => (ok?: vec!["a", "b", "c"], ""),
        "a,b,c 23" => (ok: vec!["a", "b", "c"], " 23"),
        "23" => (ok: Vec::<&str>::new(), "23"),
        "" => (ok?: Vec::<&str>::new(), ""),
        "a,b,,c" => (ok: vec!["a", "b"], ",,c"),
    );
}

#[test]
fn test_joined1() {
    test!(joined1(char_exact(','), str_identifier()):
        "a" => (ok?: vec!["a"], ""),
        "a,b,c" => (ok?: vec!["a", "b", "c"], ""),
        "a,b,c 23" => (ok: vec!["a", "b", "c"], " 23"),
        "23" => (err: Error::AtLeast(1, 0), (0, 1, 1)),
        "" => (err?: Error::AtLeast(1, 0), (0, 1, 1)),
        "a,b,,c" => (ok: vec!["a", "b"], ",,c"),
    );
}

#[test]
fn nothing() {
    test!(nothing():
        "" => (ok: (), ""),
        " " => (ok: (), " "),
        "foo" => (ok: (), "foo"),
    );
}

#[test]
fn list() {
    let comma = par::char_exact::<TestError>(',');
    test!(list(0, &comma, str_identifier(), optional(&comma)):
        "" => (ok?: Vec::<&str>::new(), ""),
        " " => (ok: Vec::<&str>::new(), " "),
        "a" => (ok?: vec!["a"], ""),
        "a " => (ok: vec!["a"], " "),
        "a, " => (ok: vec!["a"], " "),
        "a,b" => (ok?: vec!["a", "b"], ""),
        "a,b " => (ok: vec!["a", "b"], " "),
        "a,b, " => (ok: vec!["a", "b"], " "),
        "a,b,23 " => (ok: vec!["a", "b"], "23 "),
    );
    test!(list(1, str_exact("::"), str_identifier(), nothing()):
        "" => (err?: Error::AtLeast(1, 0), (0, 1, 1)),
        "foo" => (ok?: vec!["foo"], ""),
        "foo " => (ok: vec!["foo"], " "),
        "foo::bar" => (ok?: vec!["foo", "bar"], ""),
        "foo::bar " => (ok: vec!["foo", "bar"], " "),
        "foo::23" => (ok: vec!["foo"], "::23"),
        "foo::" => (ok?: vec!["foo"], "::"),
    );
    test!(list(2, char_exact('.'), str_identifier(), char_exact('!')):
        "foo.bar!" => (ok?: vec!["foo", "bar"], ""),
        "foo.bar! " => (ok: vec!["foo", "bar"], " "),
        "foo.bar" => (err?: Error::ListEnd, (7, 1, 8)),
        "foo.23" => (err: Error::ListEnd, (3, 1, 4)),
        "foo." => (err?: Error::ListEnd, (3, 1, 4)),
        "foo" => (err?: Error::ListEnd, (3, 1, 4)),
        "foo!" => (err?: Error::AtLeast(2, 1), (0, 1, 1)),
    );
}

#[test]
fn char_exact() {
    test!(char_exact('x'):
        "x" => (ok: 'x', ""),
        "xy" => (ok: 'x', "y"),
        "xx" => (ok: 'x', "x"),
        "y" => (err: Error::CharExact('x'), (0, 1, 1)),
        "" => (err?: Error::CharExact('x'), (0, 1, 1)),
    );
}

#[test]
fn take_right() {
    test!(take_right(str_exact("foo"), str_exact("bar")):
        "foobar" => (ok: "bar", ""),
        "foobarbaz" => (ok: "bar", "baz"),
        "foob" => (err?: Error::StrExact("bar"), (3, 1, 4)),
        "foo" => (err?: Error::StrExact("bar"), (3, 1, 4)),
        "foobyr" => (err: Error::StrExact("bar"), (3, 1, 4)),
        "f" => (err?: Error::StrExact("foo"), (0, 1, 1)),
        "" => (err?: Error::StrExact("foo"), (0, 1, 1)),
        "fyybar" => (err: Error::StrExact("foo"), (0, 1, 1)),
    );
}

#[test]
fn optional() {
    test!(optional(str_identifier()):
        "foo" => (ok?: Some("foo"), ""),
        "foo " => (ok: Some("foo"), " "),
        "" => (ok?: None, ""),
        " " => (ok: None, " "),
        "23 " => (ok: None, "23 "),
    );
}

#[test]
fn delimited() {
    test!(delimited(str_identifier(), str_whitespace(), str_keyword("b")):
        "a b" => (ok?: " ", ""),
        "a b " => (ok: " ", " "),
    );
    test!(delimited(str_exact("("), str_identifier(), str_exact(")")):
        "(foo)" => (ok: "foo", ""),
        "(foo." => (err: Error::StrExact(")"), (4, 1, 5)),
        "(foo )" => (err: Error::StrExact(")"), (4, 1, 5)),
        "(foo" => (err?: Error::StrExact(")"), (4, 1, 5)),
        "( foo" => (err: Error::StrIdentifier, (1, 1, 2)),
        "(23" => (err: Error::StrIdentifier, (1, 1, 2)),
        "(" => (err?: Error::StrIdentifier, (1, 1, 2)),
        "()" => (err: Error::StrIdentifier, (1, 1, 2)),
        "23" => (err: Error::StrExact("("), (0, 1, 1)),
        "" => (err?: Error::StrExact("("), (0, 1, 1)),
    );
}

#[test]
fn combine() {
    test!(combine(str_exact("foo"), str_exact("bar"), |a, b| (a, b)):
        "foobar" => (ok: ("foo", "bar"), ""),
        "foobarbaz" => (ok: ("foo", "bar"), "baz"),
        "fyybarbaz" => (err: Error::StrExact("foo"), (0, 1, 1)),
        "foobyrbaz" => (err: Error::StrExact("bar"), (3, 1, 4)),
        "foob" => (err?: Error::StrExact("bar"), (3, 1, 4)),
        "foo" => (err?: Error::StrExact("bar"), (3, 1, 4)),
        "f" => (err?: Error::StrExact("foo"), (0, 1, 1)),
        "" => (err?: Error::StrExact("foo"), (0, 1, 1)),
    );
}

#[test]
fn str_exact() {
    test!(str_exact("foo"):
        "foo" => (ok: "foo", ""),
        "foobar" => (ok: "foo", "bar"),
        "foo " => (ok: "foo", " "),
        "bar" => (err: Error::StrExact("foo"), (0, 1, 1)),
        "f" => (err?: Error::StrExact("foo"), (0, 1, 1)),
        "f " => (err: Error::StrExact("foo"), (0, 1, 1)),
        "" => (err?: Error::StrExact("foo"), (0, 1, 1)),
    );
}

#[test]
fn str_keyword() {
    test!(str_keyword("foo_bar"):
        "foo_bar" => (ok?: "foo_bar", ""),
        "foo_bar " => (ok: "foo_bar", " "),
        "foo_bar_baz" => (err: Error::StrKeyword("foo_bar"), (0, 1, 1)),
        "foo" => (err?: Error::StrKeyword("foo_bar"), (0, 1, 1)),
        "bar" => (err: Error::StrKeyword("foo_bar"), (0, 1, 1)),
        "" => (err?: Error::StrKeyword("foo_bar"), (0, 1, 1)),
    );
}

#[test]
fn str_identifier() {
    test!(str_identifier():
        "f" => (ok?: "f", ""),
        "foo" => (ok?: "foo", ""),
        "foo_barBAZ23" => (ok?: "foo_barBAZ23", ""),
        "f " => (ok: "f", " "),
        "_ " => (ok: "_", " "),
        "foo " => (ok: "foo", " "),
        "_foo " => (ok: "_foo", " "),
        "" => (err?: Error::StrIdentifier, (0, 1, 1)),
        "23" => (err: Error::StrIdentifier, (0, 1, 1)),
        " foo" => (err: Error::StrIdentifier, (0, 1, 1)),
    );
}

#[test]
fn str_whitespace() {
    test!(str_whitespace():
        " " => (ok?: " ", ""),
        "\t" => (ok?: "\t", ""),
        "\n" => (ok?: "\n", ""),
        "   \n\n  \t \t  " => (ok?: "   \n\n  \t \t  ", ""),
        "   foo" => (ok: "   ", "foo"),
        "" => (err?: Error::StrWhitespace, (0, 1, 1)),
        "foo" => (err: Error::StrWhitespace, (0, 1, 1)),
    );
}
