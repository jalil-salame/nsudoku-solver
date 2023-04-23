use std::{num::NonZeroU8, ops::ControlFlow};

use crate::{SolvedSudoku, Sudoku, SudokuValue};

use thiserror::Error;

#[derive(Debug, Clone, Error, PartialEq, Eq)]
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
            debug_assert_ne!(self.0.get(), u8::MAX);
            // Safety: This can only be 0 if self.0.get() == u8::MAX, this could only happen if
            // self.0 > max.0 which is very undefined
            Some(Self(unsafe { NonZeroU8::new_unchecked(self.0.get() + 1) }))
        }
    }
}

impl super::Sudoku {
    fn validate_chage_at(&self, (x, y): (usize, usize), new_value: Option<SudokuValue>) -> bool {
        let no_dupe_in_row = || {
            self.values
                .row(x)
                .indexed_iter()
                .all(|(iy, &val)| iy == y || val != new_value)
        };
        let no_dupe_in_col = || {
            self.values
                .column(y)
                .indexed_iter()
                .all(|(ix, &val)| ix == x || val != new_value)
        };
        let no_dupe_in_cell = || {
            self.values
                .exact_chunks((self.grid_w, self.grid_w))
                .into_iter()
                .nth(y / self.grid_w + (x / self.grid_w) * self.grid_w)
                .unwrap()
                .indexed_iter()
                .all(|((ix, iy), &val)| {
                    (ix == x % self.grid_w && iy == y % self.grid_w) || val != new_value
                })
        };
        no_dupe_in_row() && no_dupe_in_col() && no_dupe_in_cell()
    }
}

#[derive(Debug, Default, Clone)]
pub struct IterativeDfs {
    empty: Vec<(usize, usize)>,
}

impl Solver for IterativeDfs {
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
            // Safety: when finding empty cells the index returned should always be valid, this is
            // only false if resized, which should never happen (Sudokus are a fixed size after
            // being created)
            let (x, y) = *unsafe { self.empty.get_unchecked(ix) };

            // Update empty value
            let value = sudoku.values.get_mut((x, y)).expect("valid coordinate");
            let new_value = if let Some(sval) = value {
                if let Some(sval) = sval.next(max) {
                    Some(sval)
                } else {
                    // Exhausted possibilities for cell
                    if ix == 0 {
                        return Err(Error::NotSolvable);
                    }
                    *value = None;
                    ix -= 1;
                    continue;
                }
            } else {
                // Safety: the literal value 1 is never 0
                Some(unsafe { NonZeroU8::new_unchecked(1) }.into())
            };
            *value = new_value;
            if sudoku.validate_chage_at((x, y), new_value) {
                ix += 1;
            }
        }
        // Sudoku has been solved
        Ok(sudoku.solved())
    }
}

#[derive(Debug, Default, Clone)]
pub struct RecursiveDfs;

impl RecursiveDfs {
    fn recurse(sudoku: &mut Sudoku) -> ControlFlow<()> {
        let max = sudoku.max_value().0.get();
        // Get an empty cell
        let Some((ix, _)) = sudoku.values.indexed_iter().find(|(_, val)| val.is_none()) else { return ControlFlow::Break(()); };
        // Try different values for the empty cell
        for value in 1..=max {
            // Safety: The range ``1..=max`` will never produce ``0``
            let new_value = Some(unsafe { NonZeroU8::new_unchecked(value) }.into());
            let empty = sudoku.values.get_mut(ix).unwrap();
            *empty = new_value;
            // Ensure valid Sudoku
            if sudoku.validate_chage_at(ix, new_value) {
                // Try setting another cell
                Self::recurse(sudoku)?;
            }
        }
        // Set cell as empty
        let empty = sudoku.values.get_mut(ix).unwrap();
        *empty = None;
        // No value was right
        ControlFlow::Continue(())
    }
}

impl Solver for RecursiveDfs {
    fn solve(&mut self, mut sudoku: Sudoku) -> Result<SolvedSudoku, Error> {
        match Self::recurse(&mut sudoku) {
            ControlFlow::Continue(_) => Err(Error::NotSolvable),
            ControlFlow::Break(_) => Ok(sudoku.try_solved().unwrap()),
        }
    }
}

#[cfg(test)]
mod test {
    use super::{IterativeDfs, RecursiveDfs, Solver};
    use crate::{solver::Error, Sudoku};

    #[allow(unused_imports)]
    use pretty_assertions::{assert_eq, assert_ne};

    fn test_solver_on_empty_sudoku(solver: &mut impl Solver, grid_w: usize) {
        let width = grid_w * grid_w;
        let empty = Sudoku::empty(grid_w);
        assert_ne!(
            solver.solve(empty),
            Err(Error::NotSolvable),
            "Couldn't solve {width}×{width} empty Sudoku"
        );
    }

    #[test]
    fn iterative_dfs_solve_empty() {
        let mut solver = IterativeDfs::default();
        for grid_w in 2..=4 {
            test_solver_on_empty_sudoku(&mut solver, grid_w);
        }
    }

    #[test]
    fn recursive_dfs_solve_empty() {
        let mut solver = RecursiveDfs::default();
        let grid_w = 2;
        test_solver_on_empty_sudoku(&mut solver, grid_w);
    }
}
