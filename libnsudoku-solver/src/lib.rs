use std::num::NonZeroU8;

use ndarray::Array2;
use thiserror::Error;

#[cfg(test)]
#[allow(unused)]
use pretty_assertions::{assert_eq, assert_ne};

/// Errors returned by functions creating Sudokus
#[derive(Debug, Error, PartialEq, Eq)]
pub enum SudokuError {
    #[error("Invalid grid width: {grid_w}, expected value in range (2..=15)")]
    InvalidGridWidth { grid_w: usize },
    #[error("Invalid value for Sudoku, expected value in range 1..={max} got {value}")]
    InvalidValue { value: u8, max: usize },
    #[error("Invalid number of values for Sudoku, expected {expected} got {len}")]
    InvalidValuesAmount { len: usize, expected: usize },
    #[error("{sudoku}\nIs not a solved sudoku")]
    NotSolved { sudoku: Sudoku },
    #[error("{sudoku}\nHas a wrong value at {pos:?}")]
    WrongValueSet { sudoku: Sudoku, pos: (usize, usize) },
}

pub type Result<T> = core::result::Result<T, SudokuError>;

/// An unsolved Sudoku
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sudoku {
    /// The width of the grid
    ///
    /// A 9x9 Sudoku has a √9 = 3 grid_w
    ///
    /// # Invariants
    ///
    /// - Valid values for a Sudoku are 1..=grid_w²
    /// - The number of cells is grid_w⁴
    grid_w: usize,
    /// The Sudoku Values
    ///
    /// # Invariants
    ///
    /// - `None` when empty
    /// - In range 1..=grid_w² otherwise
    values: Array2<Option<SudokuValue>>,
}

impl Sudoku {
    /// Create an empty Sudoku with grid width `grid_w`
    ///
    /// **Panics** if `grid_w` is not valid (`Self::valid_grid_width`)
    pub fn empty(grid_w: usize) -> Self {
        Self::try_empty(grid_w).unwrap()
    }

    /// Create an empty Sudoku with grid width `grid_w`
    ///
    /// Returns `None` if the `grid_w` is invalid (`Self::valid_grid_width`)
    pub fn try_empty(grid_w: usize) -> Result<Self> {
        Self::valid_grid_width(grid_w)
            .then(|| {
                // Safety: we check that the `grid_w` is valid
                unsafe { Self::empty_unchecked(grid_w) }
            })
            .ok_or(SudokuError::InvalidGridWidth { grid_w })
    }

    /// Create an empty Sudoku with grid width `grid_w`
    ///
    /// # Safety
    ///
    /// The grid width (`grid_w`) must be valid (`Self::valid_grid_width`)
    pub unsafe fn empty_unchecked(grid_w: usize) -> Self {
        // debug: Make sure invariants are met
        debug_assert!(Self::valid_grid_width(grid_w), "Invalid grid width");
        Self {
            grid_w,
            values: Array2::default((grid_w * grid_w, grid_w * grid_w)),
        }
    }

    /// Create a Sudoku with grid width `grid_w` with the provided values
    ///
    /// **Panics**
    ///
    /// - `grid_w` is invalid
    /// - `values.len()` is not `grid_w⁴`
    /// - The values are not valid for the size of the Sudoku
    pub fn new(grid_w: usize, values: Vec<Option<SudokuValue>>) -> Self {
        Self::try_new(grid_w, values).unwrap()
    }

    /// Create a Sudoku with grid width `grid_w` with the provided values
    ///
    /// **Fails**
    ///
    /// - `grid_w` is invalid
    /// - `values.len()` is not `grid_w⁴`
    /// - The values are not valid for the size of the Sudoku
    pub fn try_new(grid_w: usize, values: Vec<Option<SudokuValue>>) -> Result<Self> {
        Self::validate_grid_width(grid_w)?;

        Self::validate_values(grid_w, values.iter().copied())?;

        // Safety: we check invariants beforehand
        Ok(unsafe { Self::new_unchecked(grid_w, values) })
    }

    /// Create a Sudoku with grid width `grid_w` with the provided values
    ///
    /// # Safety
    ///
    /// - `grid_w` must be valid
    /// - `values.len() == grid_w⁴`
    /// - All the values in `values` must be valid for the size of the Sudoku
    pub unsafe fn new_unchecked(grid_w: usize, values: Vec<Option<SudokuValue>>) -> Self {
        // debug: check invariants
        debug_assert!(
            Self::validate_grid_width(grid_w).is_ok(),
            "Invalid grid width"
        );
        debug_assert!(
            Self::validate_values(grid_w, values.iter().copied()).is_ok(),
            "Invalid values"
        );

        Self {
            grid_w,
            values: Array2::from_shape_vec_unchecked((grid_w * grid_w, grid_w * grid_w), values),
        }
    }

    /// The maximum valid SudokuValue for this Sudoku
    #[inline]
    pub fn max_value(&self) -> SudokuValue {
        SudokuValue(
            ((self.grid_w * self.grid_w) as u8)
                .try_into()
                .expect("valid `grid_w`"),
        )
    }

    /// Checks if `grid_w` is a valid grid width
    #[inline]
    pub fn valid_grid_width(grid_w: usize) -> bool {
        Self::validate_grid_width(grid_w).is_ok()
    }

    /// Checks if `grid_w` is a valid grid width
    #[inline]
    pub fn validate_grid_width(grid_w: usize) -> Result<()> {
        if !(2..=15).contains(&grid_w) {
            return Err(SudokuError::InvalidGridWidth { grid_w });
        }
        Ok(())
    }

    /// Checks if `value` is a valid `SudokuValue` for a Sudoku with grid width `grid_w`
    #[inline]
    pub fn valid_value(grid_w: usize, value: SudokuValue) -> bool {
        (1..=(grid_w * grid_w) as u8).contains(&value.0.get())
    }

    /// Checks if all values are valid values
    #[inline]
    pub fn valid_values(
        grid_w: usize,
        values: impl ExactSizeIterator<Item = Option<SudokuValue>>,
    ) -> bool {
        Self::validate_values(grid_w, values).is_ok()
    }

    /// Checks if there are enough values and all values are valid for the specified Sudoku size
    #[inline]
    pub fn validate_values(
        grid_w: usize,
        values: impl ExactSizeIterator<Item = Option<SudokuValue>>,
    ) -> Result<()> {
        // Correct number of values
        let expected = grid_w * grid_w * grid_w * grid_w;
        if values.len() != expected {
            return Err(SudokuError::InvalidValuesAmount {
                len: values.len(),
                expected,
            });
        }

        // Values are Valid
        if let Some(value) = values
            .flatten()
            .find(|&value| !Self::valid_value(grid_w, value))
            .map(|value| value.0.get())
        {
            Err(SudokuError::InvalidValue {
                value,
                max: grid_w * grid_w,
            })
        } else {
            Ok(())
        }
    }

    /// Convert into a solved Sudoku
    ///
    /// **Panics** if
    ///
    /// - Any value is empty
    /// - Any value is wrong
    pub fn solved(self) -> SolvedSudoku {
        self.try_solved().unwrap()
    }

    /// Try to convert this Sudoku into a solved Sudoku
    pub fn try_solved(self) -> Result<SolvedSudoku> {
        let Sudoku { grid_w: _, values } = &self;
        if values.iter().any(Option::is_none) {
            return Err(SudokuError::NotSolved { sudoku: self });
        }

        let Sudoku { grid_w, values } = self;
        let values = values.mapv(Option::unwrap);

        // Verify Rows
        let mut vals: Vec<SudokuValue> = Vec::with_capacity(grid_w * grid_w);
        for (iy, row) in values.rows().into_iter().enumerate() {
            vals.clear();
            vals.extend(row);
            if let Some(ix) = vals
                .iter()
                .enumerate()
                .position(|(k, val)| vals[k + 1..].contains(val))
            {
                return Err(SudokuError::WrongValueSet {
                    sudoku: Sudoku {
                        grid_w,
                        values: values.mapv(Some),
                    },
                    pos: (ix, iy),
                });
            }
        }

        // Verify Columns
        for (ix, col) in values.columns().into_iter().enumerate() {
            vals.clear();
            vals.extend(col);
            if let Some(iy) = vals
                .iter()
                .enumerate()
                .position(|(k, val)| vals[k + 1..].contains(val))
            {
                return Err(SudokuError::WrongValueSet {
                    sudoku: Sudoku {
                        grid_w,
                        values: values.mapv(Some),
                    },
                    pos: (ix, iy),
                });
            }
        }

        // Verify cells
        for (i, cell) in values
            .exact_chunks((grid_w, grid_w))
            .into_iter()
            .enumerate()
        {
            vals.clear();
            vals.extend(cell);
            if let Some(j) = vals
                .iter()
                .enumerate()
                .position(|(k, val)| vals[k + 1..].contains(val))
            {
                let (ix, iy) = (i % grid_w + j % grid_w, i / grid_w + j / grid_w);
                return Err(SudokuError::WrongValueSet {
                    sudoku: Sudoku {
                        grid_w,
                        values: values.mapv(Some),
                    },
                    pos: (ix, iy),
                });
            }
        }

        Ok(SolvedSudoku { grid_w, values })
    }
}

impl std::fmt::Display for Sudoku {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let num_cells = self.grid_w;
        let value_pad = if self.grid_w < 4 {
            1
        } else if self.grid_w < 10 {
            2
        } else if self.grid_w < 32 {
            3
        } else {
            unreachable!("invalid `grid_w`")
        };
        let cell_width = (value_pad + 1) * self.grid_w + 1;
        let sep_line = format!(
            "+{}",
            format!("{}+", "-".repeat(cell_width)).repeat(num_cells)
        );

        for (ix, row) in self.values.rows().into_iter().enumerate() {
            // Write separating line
            if (ix % cell_width) == 0 {
                writeln!(f, "{}", sep_line)?;
            }

            for (ix, value) in row.into_iter().enumerate() {
                // Cell separator
                if ix % cell_width == 0 {
                    write!(f, "|")?;
                }

                if let Some(value) = value {
                    write!(f, " {:>value_pad$}", value)?;
                } else {
                    write!(f, " {:>value_pad$}", '.')?;
                }
            }
            writeln!(f, " |")?;
        }

        write!(f, "{}", sep_line)
    }
}

/// A solved Sudoku
///
/// All values are non empty and fullfill the Sudoku invariants
#[allow(unused)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolvedSudoku {
    grid_w: usize,
    values: Array2<SudokuValue>,
}

impl TryFrom<Sudoku> for SolvedSudoku {
    type Error = SudokuError;

    fn try_from(sudoku: Sudoku) -> std::result::Result<Self, Self::Error> {
        sudoku.try_solved()
    }
}

/// The value of a cell in the Sudoku
///
/// Limits grid size to 15x15 as it can only represent values up to 255 (16x16 grids require 256 to
/// be representable)
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SudokuValue(NonZeroU8);

impl From<NonZeroU8> for SudokuValue {
    fn from(value: NonZeroU8) -> Self {
        Self(value)
    }
}

impl core::fmt::Display for SudokuValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0.get())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[allow(unused)]
    use pretty_assertions::{assert_eq, assert_ne};

    #[test]
    fn sudoku_2x2_bad_value() {
        let s = Sudoku::try_new(
            2,
            [1, 2, 3, 4, 5, 4, 1, 3, 4, 3, 2, 1, 2, 1, 4, 2]
                .into_iter()
                .map(NonZeroU8::new)
                .map(|val| val.map(Into::into))
                .collect(),
        );

        assert_eq!(s, Err(SudokuError::InvalidValue { value: 5, max: 4 }));
    }

    #[test]
    fn sudoku_2x2_too_few_values() {
        let s = Sudoku::try_new(
            2,
            [1, 2, 3, 4, 2, 4, 1, 3, 4, 3, 2, 1, 2, 1, 4]
                .into_iter()
                .map(NonZeroU8::new)
                .map(|val| val.map(Into::into))
                .collect(),
        );

        assert_eq!(
            s,
            Err(SudokuError::InvalidValuesAmount {
                len: 15,
                expected: 16
            })
        );
    }

    #[test]
    fn sudoku_2x2_too_many_values() {
        let s = Sudoku::try_new(
            2,
            [1, 2, 3, 4, 2, 4, 1, 3, 4, 3, 2, 1, 2, 1, 4, 2, 1]
                .into_iter()
                .map(NonZeroU8::new)
                .map(|val| val.map(Into::into))
                .collect(),
        );

        assert_eq!(
            s,
            Err(SudokuError::InvalidValuesAmount {
                len: 17,
                expected: 16
            })
        );
    }

    #[test]
    fn solved_sudoku_2x2() {
        let values: Vec<_> = [1, 2, 3, 4, 3, 4, 1, 2, 4, 3, 2, 1, 2, 1, 4, 3]
            .into_iter()
            .map(NonZeroU8::new)
            .map(|val| val.map(Into::into))
            .collect();
        let s = Sudoku::try_new(2, values.clone()).unwrap();

        assert_eq!(
            s.try_solved(),
            Ok(SolvedSudoku {
                grid_w: 2,
                values: Array2::from_shape_vec((4, 4), values.into_iter().flatten().collect())
                    .unwrap()
            })
        );
    }

    #[test]
    fn solved_sudoku_2x2_bad_row() {
        let s = Sudoku::try_new(
            2,
            [1, 1, 3, 4, 3, 4, 1, 2, 4, 3, 2, 1, 2, 1, 4, 3]
                .into_iter()
                .map(NonZeroU8::new)
                .map(|val| val.map(Into::into))
                .collect(),
        )
        .unwrap();

        assert_eq!(
            s.clone().try_solved(),
            Err(SudokuError::WrongValueSet {
                sudoku: s,
                pos: (0, 0)
            })
        );
    }

    #[test]
    fn solved_sudoku_2x2_bad_col() {
        let s = Sudoku::try_new(
            2,
            [1, 2, 3, 4, 4, 3, 1, 2, 4, 3, 2, 1, 2, 1, 4, 3]
                .into_iter()
                .map(NonZeroU8::new)
                .map(|val| val.map(Into::into))
                .collect(),
        )
        .unwrap();

        assert_eq!(
            s.clone().try_solved(),
            Err(SudokuError::WrongValueSet {
                sudoku: s,
                pos: (0, 1)
            })
        );
    }

    #[test]
    fn solved_sudoku_2x2_bad_cell() {
        let s = Sudoku::try_new(
            2,
            [1, 2, 3, 4, 2, 1, 4, 3, 3, 4, 1, 2, 4, 3, 2, 1]
                .into_iter()
                .map(NonZeroU8::new)
                .map(|val| val.map(Into::into))
                .collect(),
        )
        .unwrap();

        assert_eq!(
            s.clone().try_solved(),
            Err(SudokuError::WrongValueSet {
                sudoku: s,
                pos: (0, 0)
            })
        );
    }

    #[test]
    fn sudoku_grid_width() {
        // Too small
        for grid_w in 0..=1u8 {
            let s = Sudoku::try_empty(grid_w.into());

            assert_eq!(
                s,
                Err(SudokuError::InvalidGridWidth {
                    grid_w: grid_w.into()
                })
            )
        }

        // Too big
        for grid_w in 16..=u8::MAX {
            let s = Sudoku::try_empty(grid_w.into());

            assert_eq!(
                s,
                Err(SudokuError::InvalidGridWidth {
                    grid_w: grid_w.into()
                })
            )
        }

        // Just right
        for grid_w in 2..=15 {
            let s = Sudoku::try_empty(grid_w);

            assert_eq!(
                s,
                Ok(Sudoku::new(
                    grid_w,
                    vec![None; grid_w * grid_w * grid_w * grid_w]
                ))
            )
        }
    }
}
