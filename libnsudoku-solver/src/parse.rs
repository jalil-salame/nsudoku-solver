use std::str::FromStr;

use winnow::{
    branch::alt,
    bytes::one_of,
    character::{dec_uint, line_ending, space1},
    multi::{many1, separated1},
    prelude::*,
    sequence::{delimited, preceded, terminated},
};

use crate::{Sudoku, SudokuValue};

// use thiserror::Error;
// #[derive(Debug, Error, PartialEq, Eq)]
// #[non_exhaustive]
// #[allow(clippy::module_name_repetitions)]
// pub enum ParseSudoku<I> {
//     Winnow(I, ErrorKind),
//     Sudoku(#[from] SudokuError),
// }

// impl<I> ParseError<I> for ParseSudoku<I> {
//     fn from_error_kind(input: I, kind: ErrorKind) -> Self {
//         ParseSudoku::Winnow(input, kind)
//     }
//
//     fn append(self, _: I, _: ErrorKind) -> Self {
//         self
//     }
// }

impl FromStr for Sudoku {
    type Err = winnow::error::Error<String>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match simple_sudoku.parse(s) {
            Ok(s) => Ok(s),
            Err(_) => sudoku.parse(s).map_err(winnow::error::Error::into_owned),
        }
    }
}

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
            _ => 0, // It is invalid for these values
        };
        Sudoku::try_new(grid_w, values)
    })
    .parse_next(input)
}

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
