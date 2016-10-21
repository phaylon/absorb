
extern crate parsoid;
use parsoid::*;

fn parsed<V>(value: V, rest: &str) -> Result<V, ()> {
    Ok(Parsed { value: value, rest: rest })
}

fn parsed_we<V, E>(value: V, rest: &str) -> Result<V, E> {
    Ok(Parsed { value: value, rest: rest })
}

fn failed<V>(error: Error<()>, position: &str) -> Result<V, ()> {
    Err(Failed { error: error, position: position })
}

fn failed_we<V, E>(error: Error<E>, position: &str) -> Result<V, E> {
    Err(Failed { error: error, position: position })
}

#[derive( Debug, Clone, PartialEq, Eq )]
struct Wrap<T>(T);

#[test]
fn test_nothing() {
    assert_eq!(nothing()(""), parsed((), ""));
    assert_eq!(nothing()("foo"), parsed((), "foo"));
}

#[test]
fn test_list() {
    let comma = char_exact(',');
    let idents = list(0, &comma, identifier(), optional(&comma));
    assert_eq!(idents("a,b,c"), parsed(vec!["a", "b", "c"], ""));
    assert_eq!(idents("a,b,c,23"), parsed(vec!["a", "b", "c"], "23"));
    assert_eq!(idents("a,b,c,"), parsed(vec!["a", "b", "c"], ""));
    assert_eq!(idents("23"), parsed(vec![], "23"));
    let namespace = list(1, str_exact("::"), identifier(), nothing());
    assert_eq!(namespace("a::b::c"), parsed(vec!["a", "b", "c"], ""));
    assert_eq!(namespace("a"), parsed(vec!["a"], ""));
    assert_eq!(namespace("a::"), parsed(vec!["a"], "::"));
    assert_eq!(namespace("::"), failed(Error::AtLeast(1, 0), "::"));
}

#[test]
fn test_any() {
    let parser = any(any(str_exact("foo"), str_exact("bar")), error("fail"));
    assert_eq!(parser("foo"), parsed_we("foo", ""));
    assert_eq!(parser("bar"), parsed_we("bar", ""));
    assert_eq!(parser("qux"), failed_we(Error::Custom("fail"), "qux"));
}

#[test]
fn test_position() {
    let input = "   \n   \n   foo bar";
    let parser = take_right(whitespace(), take_right(identifier(), position()));
    let result = parser(input);
    assert_eq!(result, parsed(" bar", " bar"));
    let position = result.unwrap().value;
    assert_eq!(
        Location::from_position(input, position),
        Some(Location {
            line: 3,
            column: 7,
            position: 14,
        })
    );
}

#[test]
fn test_document() {
    assert_eq!(
        document::<(), _, _>("foo", identifier()),
        Ok("foo")
    );
    assert_eq!(
        document::<(), _, _>("23", identifier()),
        Err(DocumentError {
            error: Error::Identifier,
            location: Location {
                position: 0,
                line: 1,
                column: 1,
            },
        })
    );
    assert_eq!(
        document::<(), _, _>("  \n  \n    23", take_right(whitespace(), identifier())),
        Err(DocumentError {
            error: Error::Identifier,
            location: Location {
                position: 10,
                line: 3,
                column: 5,
            },
        })
    );
}

#[test]
fn test_str_until() {
    assert_eq!(str_until(newline())("foo\nbar"), parsed("foo", "bar"));
    assert_eq!(str_until(newline())("foo\n"), parsed("foo", ""));
    assert_eq!(str_until(newline())("\nbar"), parsed("", "bar"));
    assert_eq!(str_until(newline())("\n"), parsed("", ""));
    assert_eq!(str_until(newline())(""), parsed("", ""));
    assert_eq!(str_until(newline())("foo bar"), parsed("foo bar", ""));
}

#[test]
fn test_error_from() {
    assert_eq!(
        error_from::<_, (), _>(|| 23)("foo"),
        Err(Failed { error: Error::Custom(23), position: "foo" })
    );
    assert_eq!(
        either(str_exact("foo"), error_from(|| 23))("foo"),
        Ok(Parsed { value: "foo", rest: "" })
    );
    assert_eq!(
        either(str_exact("foo"), error_from(|| 23))("bar"),
        Err(Failed {
            error: Error::Either(Box::new((Error::StrExact("foo"), Error::Custom(23)))),
            position: "bar",
        })
    );
}

#[test]
fn test_error() {
    assert_eq!(
        error::<_, ()>(23)("foo"),
        Err(Failed { error: Error::Custom(23), position: "foo" })
    );
    assert_eq!(
        either(str_exact("foo"), error(23))("foo"),
        Ok(Parsed { value: "foo", rest: "" })
    );
    assert_eq!(
        either(str_exact("foo"), error(23))("bar"),
        Err(Failed {
            error: Error::Either(Box::new((Error::StrExact("foo"), Error::Custom(23)))),
            position: "bar",
        })
    );
}

#[test]
fn test_value_from() {
    assert_eq!(value_from(|| 23)("foo"), parsed(23, "foo"));
    assert_eq!(either(identifier(), value_from(|| "foo"))("bar"), parsed("bar", ""));
    assert_eq!(either(identifier(), value_from(|| "foo"))("23"), parsed("foo", "23"));
}

#[test]
fn test_value() {
    assert_eq!(value(23)("foo"), parsed(23, "foo"));
    assert_eq!(either(identifier(), value("foo"))("bar"), parsed("bar", ""));
    assert_eq!(either(identifier(), value("foo"))("23"), parsed("foo", "23"));
}

#[test]
fn test_take_right() {
    let parser = take_right(str_exact("foo"), str_exact("bar"));
    assert_eq!(parser("foobar"), parsed("bar", ""));
    assert_eq!(parser("foobaz"), failed(Error::StrExact("bar"), "baz"));
    assert_eq!(parser("fyybar"), failed(Error::StrExact("foo"), "fyybar"));
}

#[test]
fn test_take_left() {
    let parser = take_left(str_exact("foo"), str_exact("bar"));
    assert_eq!(parser("foobar"), parsed("foo", ""));
    assert_eq!(parser("foobaz"), failed(Error::StrExact("bar"), "baz"));
    assert_eq!(parser("fyybar"), failed(Error::StrExact("foo"), "fyybar"));
}

#[test]
fn test_map_parsed() {
    assert_eq!(map_parsed(identifier(), |v| Wrap(v))("foo"), parsed(Wrap("foo"), ""));
    assert_eq!(map_parsed(identifier(), |v| Wrap(v))("foo "), parsed(Wrap("foo"), " "));
    assert_eq!(
        map_parsed(identifier(), |v| Wrap(v))("23"),
        failed(Error::Identifier, "23")
    );
}

#[test]
fn test_map_failed() {
    assert_eq!(
        map_failed(identifier::<()>(), |e| Box::new(e))("foo"),
        Ok(Parsed { value: "foo", rest: "" })
    );
    assert_eq!(
        map_failed(identifier::<()>(), |e| Box::new(e))("23"),
        Err(Failed {
            error: Error::Custom(Box::new(Error::Identifier)),
            position: "23",
        })
    );
}

#[test]
fn test_fmap_parsed() {
    assert_eq!(fmap_parsed(identifier(), |v| Ok(Wrap(v)))("foo"), parsed(Wrap("foo"), ""));
    assert_eq!(fmap_parsed(identifier(), |v| Ok(Wrap(v)))("foo "), parsed(Wrap("foo"), " "));
    assert_eq!(
        fmap_parsed(identifier(), |v| Ok(Wrap(v)))("23"),
        failed(Error::Identifier, "23")
    );
    assert_eq!(
        fmap_parsed::<_, _, _, _, Wrap<&str>>(identifier(), |v| Err(Wrap(v)))("foo"),
        Err(Failed { error: Error::Custom(Wrap("foo")), position: "foo" })
    );
    assert_eq!(
        fmap_parsed::<_, _, _, _, Wrap<&str>>(identifier(), |v| Err(Wrap(v)))("23"),
        Err(Failed { error: Error::Identifier, position: "23" })
    );
}

#[test]
fn test_fmap_failed() {
    assert_eq!(
        fmap_failed::<Box<Error<()>>, _, _, _, _>(identifier(), |e| Err(Box::new(e)))("23"),
        Err(Failed { error: Error::Custom(Box::new(Error::Identifier)), position: "23" })
    );
    assert_eq!(
        fmap_failed::<(), _, _, _, &str>(identifier(), |_| Ok("ok"))("23"),
        Ok(Parsed { value: "ok", rest: "23" })
    );
    assert_eq!(
        fmap_failed::<(), _, _, _, &str>(identifier(), |_| Ok("ok"))("foo"),
        Ok(Parsed { value: "foo", rest: "" })
    );
}

#[test]
fn test_end_of_line() {
    assert_eq!(end_of_line()(""), parsed(None, ""));
    assert_eq!(end_of_line()("\n"), parsed(Some("\n"), ""));
    assert_eq!(
        end_of_line()(" "),
        failed(Error::Either(Box::new((Error::CharExact('\n'), Error::EndOfInput))), " ")
    );
}

#[test]
fn test_newline() {
    assert_eq!(newline()("\n\n "), parsed("\n", "\n "));
    assert_eq!(newline()("\n"), parsed("\n", ""));
    assert_eq!(newline()("\t"), failed(Error::CharExact('\n'), "\t"));
    assert_eq!(newline()(""), failed(Error::CharExact('\n'), ""));
}

#[test]
fn test_char_exact() {
    assert_eq!(char_exact('x')("x"), parsed("x", ""));
    assert_eq!(char_exact('x')("xyz"), parsed("x", "yz"));
    assert_eq!(char_exact('x')("xxx"), parsed("x", "xx"));
    assert_eq!(char_exact('x')("y"), failed(Error::CharExact('x'), "y"));
    assert_eq!(char_exact('x')(""), failed(Error::CharExact('x'), ""));
}

#[test]
fn test_end_of_input() {
    assert_eq!(end_of_input()(""), parsed((), ""));
    assert_eq!(end_of_input()(" "), failed(Error::EndOfInput, " "));
}

#[test]
fn test_many0() {
    assert_eq!(many0(str_exact("foo"))("foo"), parsed(vec!["foo"], ""));
    assert_eq!(many0(str_exact("foo"))("foobar"), parsed(vec!["foo"], "bar"));
    assert_eq!(many0(str_exact("foo"))("foofoo"), parsed(vec!["foo", "foo"], ""));
    assert_eq!(many0(str_exact("foo"))("foofoobar"), parsed(vec!["foo", "foo"], "bar"));
    assert_eq!(many0(str_exact("foo"))("bar"), parsed(vec![], "bar"));
}

#[test]
fn test_many1() {
    assert_eq!(many1(str_exact("foo"))("foo"), parsed(vec!["foo"], ""));
    assert_eq!(many1(str_exact("foo"))("foobar"), parsed(vec!["foo"], "bar"));
    assert_eq!(many1(str_exact("foo"))("foofoo"), parsed(vec!["foo", "foo"], ""));
    assert_eq!(many1(str_exact("foo"))("foofoobar"), parsed(vec!["foo", "foo"], "bar"));
    assert_eq!(many1(str_exact("foo"))("bar"), failed(Error::AtLeast(1, 0), "bar"));
}

#[test]
fn test_either() {
    let parser = either(str_exact("foo"), str_exact("bar"));
    assert_eq!(parser("foo"), parsed("foo", ""));
    assert_eq!(parser("foobar"), parsed("foo", "bar"));
    assert_eq!(parser("bar"), parsed("bar", ""));
    assert_eq!(
        parser("baz"),
        failed(Error::Either(Box::new((Error::StrExact("foo"), Error::StrExact("bar")))), "baz")
    );
}

#[test]
fn test_separated0() {
    let parser = separated0(str_exact(","), identifier());
    assert_eq!(parser("a"), parsed(vec!["a"], ""));
    assert_eq!(parser("a,b,c"), parsed(vec!["a", "b", "c"], ""));
    assert_eq!(parser("a,b,c 23"), parsed(vec!["a", "b", "c"], " 23"));
    assert_eq!(parser("23"), parsed(vec![], "23"));
    assert_eq!(parser(",23"), parsed(vec![], ",23"));
    assert_eq!(parser("a,b,,c"), parsed(vec!["a", "b"], ",c"));
}

#[test]
fn test_separated1() {
    let parser = separated1(str_exact(","), identifier());
    assert_eq!(parser("a"), parsed(vec!["a"], ""));
    assert_eq!(parser("a,b,c"), parsed(vec!["a", "b", "c"], ""));
    assert_eq!(parser("a,b,c 23"), parsed(vec!["a", "b", "c"], " 23"));
    assert_eq!(parser("23"), failed(Error::AtLeast(1, 0), "23"));
    assert_eq!(parser(",23"), failed(Error::AtLeast(1, 0), ",23"));
    assert_eq!(parser("a,b,,c"), parsed(vec!["a", "b"], ",c"));
}

#[test]
fn test_joined0() {
    let parser = joined0(str_exact(","), identifier());
    assert_eq!(parser("a"), parsed(vec!["a"], ""));
    assert_eq!(parser("a,b,c"), parsed(vec!["a", "b", "c"], ""));
    assert_eq!(parser("a,b,c 23"), parsed(vec!["a", "b", "c"], " 23"));
    assert_eq!(parser("23"), parsed(vec![], "23"));
    assert_eq!(parser("a,b,,c"), parsed(vec!["a", "b"], ",,c"));
}

#[test]
fn test_joined1() {
    let parser = joined1(str_exact(","), identifier());
    assert_eq!(parser("a"), parsed(vec!["a"], ""));
    assert_eq!(parser("a,b,c"), parsed(vec!["a", "b", "c"], ""));
    assert_eq!(parser("a,b,c 23"), parsed(vec!["a", "b", "c"], " 23"));
    assert_eq!(parser("23"), failed(Error::AtLeast(1, 0), "23"));
    assert_eq!(parser("a,b,,c"), parsed(vec!["a", "b"], ",,c"));
}

#[test]
fn test_optional() {
    assert_eq!(optional(str_exact("foo"))("foo"), parsed(Some("foo"), ""));
    assert_eq!(optional(str_exact("foo"))("foobar"), parsed(Some("foo"), "bar"));
    assert_eq!(optional(str_exact("foo"))("fo"), parsed(None, "fo"));
}

#[test]
fn test_delimited() {
    let parser = delimited(str_exact("("), identifier(), str_exact(")"));
    assert_eq!(parser("(foo)"), parsed("foo", ""));
    assert_eq!(parser("(foo )"), failed(Error::StrExact(")"), " )"));
    assert_eq!(parser(".foo)"), failed(Error::StrExact("("), ".foo)"));
    assert_eq!(parser("(23)"), failed(Error::Identifier, "23)"));
}

#[test]
fn test_combine() {
    assert_eq!(
        combine(str_exact("foo"), str_exact("bar"), |a, b| (a, b))("foobar"),
        parsed(("foo", "bar"), "")
    );
    assert_eq!(
        combine(str_exact("foo"), str_exact("bar"), |a, b| (a, b))("foobarbaz"),
        parsed(("foo", "bar"), "baz")
    );
    assert_eq!(
        combine(str_exact("foo"), str_exact("bar"), |a, b| (a, b))("fyybarbaz"),
        failed(Error::StrExact("foo"), "fyybarbaz")
    );
    assert_eq!(
        combine(str_exact("foo"), str_exact("bar"), |a, b| (a, b))("foobyrbaz"),
        failed(Error::StrExact("bar"), "byrbaz")
    );
}

#[test]
fn test_str_exact() {
    assert_eq!(str_exact("foo")("foo"), parsed("foo", ""));
    assert_eq!(str_exact("foo")("foobar"), parsed("foo", "bar"));
    assert_eq!(str_exact("foo")("fo"), failed(Error::StrExact("foo"), "fo"));
}

#[test]
fn test_keyword() {
    assert_eq!(keyword("foo")("foo"), parsed("foo", ""));
    assert_eq!(keyword("foo")("foo bar"), parsed("foo", " bar"));
    assert_eq!(keyword("foo")("foobar"), failed(Error::Keyword("foo"), "foobar"));
    assert_eq!(keyword("foo")("bar"), failed(Error::Keyword("foo"), "bar"));
}

#[test]
fn test_identifier() {
    assert_eq!(identifier()("foo"), parsed("foo", ""));
    assert_eq!(identifier()("foo_barBAZ23"), parsed("foo_barBAZ23", ""));
    assert_eq!(identifier()("f "), parsed("f", " "));
    assert_eq!(identifier()("_ "), parsed("_", " "));
    assert_eq!(identifier()("foo "), parsed("foo", " "));
    assert_eq!(identifier()("_foo "), parsed("_foo", " "));
    assert_eq!(identifier()(""), failed(Error::Identifier, ""));
    assert_eq!(identifier()("23"), failed(Error::Identifier, "23"));
}

#[test]
fn test_whitespace() {
    assert_eq!(whitespace()(" "), parsed(" ", ""));
    assert_eq!(whitespace()("\t"), parsed("\t", ""));
    assert_eq!(whitespace()("\n"), parsed("\n", ""));
    assert_eq!(whitespace()("   "), parsed("   ", ""));
    assert_eq!(whitespace()("   foo"), parsed("   ", "foo"));
    assert_eq!(whitespace()(""), failed(Error::Whitespace, ""));
    assert_eq!(whitespace()("foo"), failed(Error::Whitespace, "foo"));
}

