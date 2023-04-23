use std::str::FromStr;

use winnow::{
    branch::alt,
    bytes::{one_of, take_while1},
    character::{dec_uint, line_ending, space1},
    combinator::opt,
    multi::{count, many1, separated1},
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
/// use libnsudoku_solver::Sudoku;
///
/// let s: Sudoku = "1234....4321....".parse().unwrap();
///
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

/// Parses a separator line
fn separator_line(grid_w: usize) -> impl Fn(&str) -> IResult<&str, ()> {
    let padding = match grid_w {
        2..=3 => 2,
        4..=9 => 3,
        10..=15 => 4,
        _ => todo!("handle error case"),
    };
    move |input: &str| {
        preceded(
            '+',
            count(
                terminated(count::<_, _, (), _, _>('-', grid_w * padding + 1), '+'),
                grid_w,
            ),
        )
        .parse_next(input)
    }
}

/// Parses a separator line and extracts the ``grid_w`` out of it
fn separator_line_grid_w<'a>(input: &'a str) -> IResult<&'a str, usize> {
    take_while1(|c: char| c == '+' || c == '-')
        .and_then(|input: &'a str| {
            let grid_w = input.bytes().filter(|&c| c == b'+').count() - 1;
            separator_line(grid_w).map(|_: ()| grid_w).parse_next(input)
        })
        .parse_next(input)
}

/// Flattens a vector of vectors
///
/// ```rust
/// use libnsudoku_solver::parse::flatten_vec;
/// let v = flatten_vec(vec![vec![1, 2], vec![3, 4]]);
/// assert_eq!(v, vec![1, 2, 3, 4]);
/// ```
pub fn flatten_vec<T>(vec: Vec<Vec<T>>) -> Vec<T> {
    let mut v = vec![];
    let additional = vec.iter().map(Vec::len).sum();

    v.reserve(additional);
    for ele in vec {
        v.extend(ele);
    }
    v
}

/// Parses a row of Sudoku cells
fn parse_row<'a>(grid_w: usize) -> impl Fn(&'a str) -> IResult<&'a str, Vec<u8>> {
    // Parse "." => 0u8, "123" => 123u8
    let sudoku_value = |input| alt(('.'.map(|_| 0), dec_uint)).parse_next(input);

    // Parses "| . 2 | . 3 |" => vec![0u8, 2u8, 0u8, 3u8]
    move |input: &'a str| {
        terminated(
            // Parses "| . 2 | . 3 |" => vec![vec![0u8, 2u8], vec![0u8, 3u8]]
            //         ^^^^^^^^^^^^
            count::<_, _, Vec<Vec<u8>>, _, _>(
                // Parses "| . 2 | . 3 |" => vec![0u8, 2u8]
                //         ^^^^^^
                delimited(
                    // Parses "| . 2 | . 3 |"
                    //         ^
                    '|',
                    // Parses "| . 2 | . 3 |" => vec![0u8, 2u8]
                    //          ^^^^
                    count::<_, _, Vec<u8>, _, _>(preceded(space1, sudoku_value), grid_w),
                    // Parses "| . 2 | . 3 |"
                    //              ^
                    space1,
                ),
                grid_w,
            ),
            // Parses "| . 2 | . 3 |"
            //                     ^
            '|',
        )
        .map(flatten_vec)
        .parse_next(input)
    }
}

/// Parses a pretty printed sudoku out of a string
///
/// ```rust
/// use libnsudoku_solver::Sudoku;
///
/// let s1: Sudoku = "1234....4321....".parse().unwrap();
/// let s2: Sudoku =
/// "+-----+-----+
/// | 1 2 | 3 4 |
/// | . . | . . |
/// +-----+-----+
/// | 4 3 | 2 1 |
/// | . . | . . |
/// +-----+-----+".parse().unwrap();
///
/// assert_eq!(s1, s2);
/// ```
fn sudoku(input: &str) -> IResult<&str, Sudoku> {
    // Extract ``grid_w``
    let (input, grid_w) = terminated(separator_line_grid_w, line_ending).parse_next(input)?;

    count(
        terminated(
            count(terminated(parse_row(grid_w), line_ending), grid_w).map(flatten_vec),
            terminated(separator_line(grid_w), opt(line_ending)),
        ),
        grid_w,
    )
    .map_res(|v| {
        let values = SudokuValue::many(flatten_vec(v));
        Sudoku::try_new(grid_w, values)
    })
    .parse_next(input)
}

#[cfg(test)]
mod test {
    use crate::Sudoku;
    #[allow(unused)]
    use pretty_assertions::{assert_eq, assert_ne};

    use super::parse_row;

    #[test]
    fn it_parses() {
        let s1: Sudoku = "1234....4321....".parse().expect("successful parse");
        let s2: Sudoku = "+-----+-----+\n| 1 2 | 3 4 |\n| . . | . . |\n+-----+-----+\n| 4 3 | 2 1 |\n| . . | . . |\n+-----+-----+"
            .parse()
            .expect("successful parse");
        assert_eq!(s1, s2);
    }

    #[test]
    fn parses_a_cell() {
        use winnow::Parser;
        let s = parse_row(2)
            .parse("| 1 2 | 3 4 |")
            .expect("successful parse");
        assert_eq!(s, vec![1, 2, 3, 4]);
    }
}
