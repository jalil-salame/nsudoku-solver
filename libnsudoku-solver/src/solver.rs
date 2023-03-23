use std::num::NonZeroU8;

use crate::{SolvedSudoku, Sudoku};

use thiserror::Error;

#[derive(Debug, Clone, Error)]
pub enum Error {
    #[error("There is no way to solve this Sudoku")]
    NotSolvable,
}

pub trait Solver {
    /// Solve the provided sudoku
    ///
    /// # Errors
    ///
    /// - If the sudoku is not solvable
    fn solve(&mut self, sudoku: Sudoku) -> Result<SolvedSudoku, Error>;
}

impl super::SudokuValue {
    fn next(self, max: Self) -> Option<Self> {
        if self == max {
            None
        } else {
            Some(Self(NonZeroU8::new(self.0.get() + 1).unwrap()))
        }
    }
}

impl super::Sudoku {
    fn validate_chage_at(&self, (x, y): (usize, usize)) -> bool {
        if let Some(value) = self.values.get((x, y)).copied() {
            let no_dupe_in_row = || {
                self.values
                    .row(y)
                    .indexed_iter()
                    .all(|(ix, &val)| ix == x || val != value)
            };
            let no_dupe_in_col = || {
                self.values
                    .column(x)
                    .indexed_iter()
                    .all(|(iy, &val)| iy == y || val != value)
            };
            let no_dupe_in_cell = || {
                self.values
                    .exact_chunks((self.grid_w, self.grid_w))
                    .into_iter()
                    .nth(x / self.grid_w + (y / self.grid_w) * self.grid_w)
                    .unwrap()
                    .indexed_iter()
                    .all(|((ix, iy), &val)| {
                        (ix == x % self.grid_w && iy == y % self.grid_w) || val != value
                    })
            };
            return no_dupe_in_row() && no_dupe_in_col() && no_dupe_in_cell();
        }
        unreachable!("Value changed should not be empty")
    }
}

#[derive(Debug, Default, Clone)]
pub struct Dfs {
    empty: Vec<(usize, usize)>,
}

impl Solver for Dfs {
    fn solve(&mut self, mut sudoku: Sudoku) -> Result<SolvedSudoku, Error> {
        self.empty.clear();
        // Find empty cells
        self.empty.extend(
            sudoku
                .values
                .indexed_iter()
                .filter_map(|(ix, value)| value.is_none().then_some(ix)),
        );
        // Fill empty values
        let max = sudoku.max_value();
        let len = self.empty.len();
        let mut ix = 0;
        while ix < len {
            debug_assert!((0..self.empty.len()).contains(&ix), "Index out of bounds");
            let (x, y) = *unsafe { self.empty.get_unchecked(ix) };
            // Update empty value
            let value = sudoku.values.get_mut((x, y)).expect("valid coordinate");
            *value = if let Some(sval) = value {
                if let Some(sval) = sval.next(max) {
                    Some(sval)
                } else {
                    // Exhausted possibilities for cell
                    if ix == 0 {
                        return Err(Error::NotSolvable);
                    }
                    ix -= 1;
                    continue;
                }
            } else {
                Some(NonZeroU8::new(1).unwrap().into())
            };
            if sudoku.validate_chage_at((x, y)) {
                ix += 1;
            }
        }
        // Sudoku has been solved
        Ok(sudoku.solved())
    }
}
