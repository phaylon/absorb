
macro_rules! test {
    ($parser:expr, $( $input:expr => ($($check:tt)*) ),* $(,)*) => {
        {
            let desc = stringify!($parser);
            $(
            test_case!($parser, desc, $input, ($($check)*));
            )*
        }
    }
}

macro_rules! test_case {
    ($parser:expr, $parser_desc:expr, $input:expr, ($($check:tt)*)) => {
        {
            let result = $crate::parse($input, $parser, None);
//            test_case_check!($parser_desc, $input, $crate::parse($input, $parser), $($check)*);
            test_case_check!($parser_desc, $input, result, $($check)*);
        }
    }
}

macro_rules! test_case_check {
    ($parser_desc:expr, $input:expr, $result:expr, ok: $value:expr, $loc:expr) => {
        test_case_ok!(
            $parser_desc, $input, $result, $value, $crate::State::Complete, $loc
        );
    };
    ($parser_desc:expr, $input:expr, $result:expr, ok?: $value:expr, $loc:expr) => {
        test_case_ok!(
            $parser_desc, $input, $result, $value, $crate::State::Incomplete, $loc
        );
    };
    ($parser_desc:expr, $input:expr, $result:expr, err: $error:expr, $loc:expr) => {
        test_case_err!(
            $parser_desc, $input, $result, $error, $crate::State::Complete, $loc
        );
    };
    ($parser_desc:expr, $input:expr, $result:expr, err?: $error:expr, $loc:expr) => {
        test_case_err!(
            $parser_desc, $input, $result, $error, $crate::State::Incomplete, $loc
        );
    };
    ($parser_desc:expr, $input:expr, $result:expr, fatal: $error:expr) => {
        test_case_fatal!($parser_desc, $input, $result, $error);
    }
}

macro_rules! test_case_fatal {
    ($parser_desc:expr, $input:expr, $result:expr, $error:expr) => {
        {
            match $result {
                Err(error) => {
                    assert!(error == $error,
                        "{} -> {:?}:\n\t! Error is not as expected.\n\t\
                            Expected: {:?}\n\tReceived: {:?}\n",
                        $parser_desc, $input,
                        $error, error
                    );
                },
                Ok(::ParseResult::Parsed(parsed)) => panic!(
                    "{} <- {:?}:\n\tExpected an Err(_) result but received Parsed({:?})\n",
                    $parser_desc, $input, parsed
                ),
                Ok(::ParseResult::Failed(failed)) => panic!(
                    "{} <- {:?}:\n\tExpected an Err(_) result but received Failed({:?})\n",
                    $parser_desc, $input, failed
                ),
            };
        }
    }
}

macro_rules! test_case_err {
    ($parser_desc:expr,
        $input:expr, $result:expr, $error:expr, $state:expr, $loc:expr
    ) => {
        {
            let (error, state, loc) = match $result {
                Ok(::ParseResult::Failed(::Failed { error, state, location })) =>
                    (error, state, location),
                other => panic!(
                    "{} <- {:?}:\n\tExpected an Ok(Failed(..)) result but received {:?}\n",
                    $parser_desc, $input, other
                ),
            };
            let expected = $error;
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
            let expected_loc = $crate::Location {
                position: $loc.0,
                line: $loc.1,
                column: $loc.2,
            };
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
                Ok(::ParseResult::Parsed(::Parsed { value, state, rest }))
                    => (value, state, rest.slice()),
                other => panic!(
                    "{} <- {:?}:\n\tExpected an Ok(Parsed(..)) result) but received {:?}\n",
                    $parser_desc, $input, other
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

