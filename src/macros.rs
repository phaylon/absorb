
macro_rules! try_parsed {
    ($e:expr) => {
        match $e {
            Ok(::ParseResult::Parsed(parsed)) => parsed,
            Ok(::ParseResult::Failed(failed)) => return Ok(::ParseResult::Failed(failed)),
            Err(error) => return Err(error),
        }
    }
}

macro_rules! try_failed {
    ($e:expr) => {
        match $e {
            Ok(::ParseResult::Parsed(parsed)) => return Ok(::ParseResult::Parsed(parsed)),
            Ok(::ParseResult::Failed(failed)) => failed,
            Err(error) => return Err(error),
        }
    }
}
