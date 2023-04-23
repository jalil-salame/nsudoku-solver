use std::str::FromStr;

use winnow::{
    branch::alt,
    bytes::one_of,
    character::{dec_uint, line_ending, space1},
    combinator::opt,
    multi::{many1, separated1},
    prelude::*,
    sequence::{delimited, preceded, terminated},
};

use crate::{Sudoku, SudokuError, SudokuValue};

impl FromStr for Sudoku {
    type Err = winnow::error::Error<String>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        alt((simple_sudoku, sudoku))
            .parse(s)
            .map_err(winnow::error::Error::into_owned)
    }
}

/// Parses many sudokus separated by newlines
///
/// # Errors
///
/// - Any sudoku is invalid (see ``Sudoku::try_new``)
/// - The format is wrong
pub fn multi_sudoku(input: &str) -> Result<Vec<Sudoku>, winnow::error::Error<String>> {
    one_sudoku_per_line
        .parse(input)
        .map_err(winnow::error::Error::into_owned)
}

/// Parses many sudokus separated by newlines
fn one_sudoku_per_line(input: &str) -> IResult<&str, Vec<Sudoku>> {
    terminated(
        separated1(alt((simple_sudoku, sudoku)), line_ending),
        opt(line_ending),
    )
    .parse_next(input)
}

/// Parse a simple sudoku out of a string
///
/// ```rust
/// let s: Sudoku = "1234....4321....".parse().unwrap();
/// assert_eq!(format!("{s}"),
/// "+-----+-----+
/// | 1 2 | 3 4 |
/// | . . | . . |
/// +-----+-----+
/// | 4 3 | 2 1 |
/// | . . | . . |
/// +-----+-----+");
/// ```
fn simple_sudoku(input: &str) -> IResult<&str, Sudoku> {
    many1(alt((
        '.'.map(|_| 0),
        one_of("0123456789").map(|c| c as u8 - b'0'),
    )))
    .map_res(|values: Vec<u8>| {
        let values: Vec<Option<SudokuValue>> = values.into_iter().map(SudokuValue::new).collect();
        let grid_w = match values.len() {
            16 => 2,
            81 => 3,
            len => return Err(SudokuError::InvalidValuesAmount { len, expected: 81 }),
        };
        Sudoku::try_new(grid_w, values)
    })
    .parse_next(input)
}

/// Parses a pretty printed sudoku out of a string
///
/// ```rust
/// let s1: Sudoku = "1234....4321....".parse().unwrap();
/// let s2: Sudoku =
/// "+-----+-----+
/// | 1 2 | 3 4 |
/// | . . | . . |
/// +-----+-----+
/// | 4 3 | 2 1 |
/// | . . | . . |
/// +-----+-----+".parse().unwrap();
/// assert_eq!(s1, s2);
/// ```
fn sudoku<'a>(input: &'a str) -> IResult<&'a str, Sudoku> {
    // Parse a separator_line: +---+---+ RE: ((+-\+)\+)+
    let separator_line = |input: &'a str| -> IResult<&'a str, ()> {
        let cell = |input: &'a str| -> IResult<&'a str, ()> { many1('-').parse_next(input) };
        delimited('+', separated1(cell, '+'), '+').parse_next(input)
    };

    // Parse out values inside cells
    let sudoku_cells = |input: &'a str| -> IResult<&'a str, Vec<u8>> {
        // Parse out values inside a row
        let sudoku_values = |input: &'a str| -> IResult<&'a str, Vec<u8>> {
            delimited(
                '|',
                separated1(
                    preceded(space1, alt(('.'.map(|_| 0), dec_uint))),
                    preceded(space1, '|'),
                ),
                preceded(space1, '|'),
            )
            .parse_next(input)
        };
        many1(terminated(sudoku_values, line_ending))
            // flatten values
            .map(|values: Vec<Vec<u8>>| values.into_iter().flatten().collect())
            .parse_next(input)
    };

    delimited(
        terminated(separator_line, line_ending),
        separated1(sudoku_cells, terminated(separator_line, line_ending)).map_res(
            |values: Vec<Vec<u8>>| {
                // flatten values and convert to sudoku values
                let values: Vec<Option<SudokuValue>> =
                    values.into_iter().flatten().map(SudokuValue::new).collect();
                // If values.len() is > 225 it is wrong anyways so we don't care about these lints
                #[allow(clippy::cast_precision_loss)]
                #[allow(clippy::cast_possible_truncation)]
                #[allow(clippy::cast_sign_loss)]
                let grid_w = (values.len() as f64).sqrt().sqrt() as usize; // Fourth root of length
                Sudoku::try_new(grid_w, values)
            },
        ),
        separator_line,
    )
    .parse_next(input)
}
