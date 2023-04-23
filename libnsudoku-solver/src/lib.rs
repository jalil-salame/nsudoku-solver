#![warn(clippy::pedantic)]
use std::num::NonZeroU8;

use ndarray::{Array2, ArrayView2};
use thiserror::Error;

pub mod parse;
pub mod solver;

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
    #[error("Is not a solved sudoku")]
    NotSolved,
    #[error("Wrong value at {pos:?}")]
    WrongValueSet { pos: (usize, usize) },
}

pub type Result<T> = core::result::Result<T, SudokuError>;

/// An unsolved Sudoku
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(remote = "Self"))]
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
    /// # Panics
    ///
    /// If `grid_w` is not valid (`Self::valid_grid_width`)
    #[must_use]
    pub fn empty(grid_w: usize) -> Self {
        Self::try_empty(grid_w).unwrap()
    }

    /// Create an empty Sudoku with grid width `grid_w`
    ///
    /// # Errors
    ///
    /// `Err` if the `grid_w` is invalid (`Self::valid_grid_width`)
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
    #[must_use]
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
    /// # Panics
    ///
    /// - `grid_w` is invalid
    /// - `values.len()` is not `grid_w⁴`
    /// - The values are not valid for the size of the Sudoku
    #[must_use]
    pub fn new(grid_w: usize, values: Vec<Option<SudokuValue>>) -> Self {
        Self::try_new(grid_w, values).unwrap()
    }

    /// Create a Sudoku with grid width `grid_w` with the provided values
    ///
    /// # Errors
    ///
    /// - `grid_w` is invalid
    /// - `values.len()` is not `grid_w⁴`
    /// - The values are not valid for the size of the Sudoku
    pub fn try_new(grid_w: usize, values: Vec<Option<SudokuValue>>) -> Result<Self> {
        Self::validate_grid_width(grid_w)?;
        // Make sure all values are in the correct range
        Self::validate_values(grid_w, &values)?;
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
    #[must_use]
    pub unsafe fn new_unchecked(grid_w: usize, values: Vec<Option<SudokuValue>>) -> Self {
        // debug: check invariants
        debug_assert!(
            Self::validate_grid_width(grid_w).is_ok(),
            "Invalid grid width"
        );
        debug_assert!(
            Self::validate_values(grid_w, &values).is_ok(),
            "Invalid values"
        );
        Self {
            grid_w,
            values: Array2::from_shape_vec_unchecked((grid_w * grid_w, grid_w * grid_w), values),
        }
    }

    /// The maximum valid `SudokuValue` for this Sudoku
    #[inline]
    #[must_use]
    pub fn max_value(&self) -> SudokuValue {
        SudokuValue(
            (std::convert::TryInto::<u8>::try_into(self.grid_w * self.grid_w)
                .expect("valid grid_w"))
            .try_into()
            .expect("valid `grid_w`"),
        )
    }

    /// Checks if `grid_w` is a valid grid width
    #[inline]
    #[must_use]
    pub fn valid_grid_width(grid_w: usize) -> bool {
        Self::validate_grid_width(grid_w).is_ok()
    }

    /// Checks if `grid_w` is a valid grid width
    ///
    /// # Errors
    ///
    /// If the `grid_w` is not valid
    #[inline]
    pub fn validate_grid_width(grid_w: usize) -> Result<()> {
        if !(2..=15).contains(&grid_w) {
            return Err(SudokuError::InvalidGridWidth { grid_w });
        }
        Ok(())
    }

    /// Checks if `value` is a valid `SudokuValue` for a Sudoku with grid width `grid_w`
    #[inline]
    #[must_use]
    pub fn valid_value(grid_w: usize, value: SudokuValue) -> bool {
        (1..=(grid_w * grid_w).try_into().expect("valid grid_w")).contains(&value.0.get())
    }

    /// Validate a Sudoku comming from an unknown source
    ///
    /// # Errors
    ///
    /// - The `grid_w` is invalid
    /// - There are too many/not enough values
    /// - The values are not in the right range
    /// - There are duplicated values in a row, column or cell
    pub fn validate_sudoku(&self) -> Result<()> {
        Self::validate_grid_width(self.grid_w)?;
        Self::validate_values(
            self.grid_w,
            self.values
                .as_slice()
                .expect("contiguous and in standard order values"),
        )
    }

    /// Checks if all values are valid values
    #[inline]
    #[must_use]
    pub fn valid_values(grid_w: usize, values: &[Option<SudokuValue>]) -> bool {
        Self::validate_values(grid_w, values).is_ok()
    }

    /// Checks if there are enough values and all values are valid for the specified Sudoku size
    ///
    /// # Errors
    ///
    /// - There are too many/not enough values
    /// - The values are not in the right range
    /// - There are duplicated values in a row, column or cell
    pub fn validate_values(grid_w: usize, values: &[Option<SudokuValue>]) -> Result<()> {
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
            .iter()
            .copied()
            .flatten()
            .find(|&value| !Self::valid_value(grid_w, value))
            .map(|value| value.0.get())
        {
            return Err(SudokuError::InvalidValue {
                value,
                max: grid_w * grid_w,
            });
        }
        let mut vals = Vec::with_capacity(grid_w * grid_w);
        let xs = ArrayView2::from_shape((grid_w * grid_w, grid_w * grid_w), values)
            .expect("grid_w and values are compatible");
        // Verify Rows
        Self::validate_rows_scratch(xs, &mut vals)?;
        // Verify Columns
        Self::validate_columns_scratch(xs, &mut vals)?;
        // Verify cells
        Self::validate_cells_scratch(grid_w, xs, &mut vals)
    }

    /// If there is a duplicate value, return its index
    fn duplicate_value_positon(vals: &[Option<SudokuValue>]) -> Option<usize> {
        vals.iter()
            .enumerate()
            .filter(|(_, val)| val.is_some())
            .position(|(i, val)| vals[i + 1..].contains(val))
    }

    /// Check if a Sudoku axis has an invalid value
    ///
    /// Returns the index of the axis, and the index of the offending element in a tuple
    ///
    /// An axis could be a row, column or cell
    ///
    /// Passing an approriately sized (``grid_w²``) vector as scratch, makes this function not allocate
    /// any extra space
    fn invalid_sudoku_axis<'a, I>(
        axis: impl IntoIterator<Item = I>,
        scratch: &'a mut Vec<Option<SudokuValue>>,
    ) -> Option<(usize, usize)>
    where
        I: IntoIterator<Item = &'a Option<SudokuValue>>,
    {
        for (i, a) in axis.into_iter().enumerate() {
            scratch.clear();
            scratch.extend(a.into_iter().copied());
            if let Some(j) = Self::duplicate_value_positon(scratch) {
                return Some((i, j));
            }
        }
        None
    }

    /// Validate the Sudoku invariants on the rows
    ///
    /// More Efficient as it doesn't need an extra allocation if you already have a buffer
    fn validate_rows_scratch(
        values: ArrayView2<Option<SudokuValue>>,
        vals: &mut Vec<Option<SudokuValue>>,
    ) -> Result<()> {
        if let Some((iy, ix)) = Self::invalid_sudoku_axis(values.rows(), vals) {
            return Err(SudokuError::WrongValueSet { pos: (ix, iy) });
        }
        Ok(())
    }

    /// Validate the sudoku invariants on the columns
    ///
    /// More Efficient as it doesn't need an extra allocation if you already have a buffer
    fn validate_columns_scratch(
        values: ArrayView2<Option<SudokuValue>>,
        vals: &mut Vec<Option<SudokuValue>>,
    ) -> Result<()> {
        if let Some((ix, iy)) = Self::invalid_sudoku_axis(values.columns(), vals) {
            return Err(SudokuError::WrongValueSet { pos: (ix, iy) });
        }
        Ok(())
    }

    /// Validate the sudoku invariants on the cells
    ///
    /// More Efficient as it doesn't need an extra allocation if you already have a buffer
    fn validate_cells_scratch(
        grid_w: usize,
        values: ArrayView2<Option<SudokuValue>>,
        vals: &mut Vec<Option<SudokuValue>>,
    ) -> Result<()> {
        if let Some((i, j)) = Self::invalid_sudoku_axis(values.exact_chunks((grid_w, grid_w)), vals)
        {
            let (ix, iy) = (i % grid_w + j % grid_w, grid_w + j / grid_w);
            return Err(SudokuError::WrongValueSet { pos: (ix, iy) });
        }
        Ok(())
    }

    /// All values are set
    pub fn filled(&self) -> bool {
        self.values.iter().all(Option::is_some)
    }

    /// Convert into a solved Sudoku
    ///
    /// # Panics
    ///
    /// - Any value is empty
    /// - Any value is wrong
    #[must_use]
    pub fn solved(self) -> SolvedSudoku {
        self.try_solved().unwrap()
    }

    /// Try to convert this Sudoku into a solved Sudoku
    ///
    /// # Errors
    ///
    /// - The sudoku is not fully filled
    /// - There are duplicated values in a row, column or cell
    pub fn try_solved(self) -> Result<SolvedSudoku> {
        let grid_w = self.grid_w;
        // Check that all values are set
        if !self.filled() {
            return Err(SudokuError::NotSolved);
        }
        let mut vals = Vec::with_capacity(grid_w * grid_w);
        let values = self.values.view();
        // Verify Rows
        Self::validate_rows_scratch(values, &mut vals)?;
        // Verify Columns
        Self::validate_columns_scratch(values, &mut vals)?;
        // Verify cells
        Self::validate_cells_scratch(grid_w, values, &mut vals)?;
        // Sudoku is solved
        Ok(SolvedSudoku {
            grid_w,
            values: self.values.mapv(Option::unwrap),
        })
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
            if (ix % num_cells) == 0 {
                writeln!(f, "{sep_line}")?;
            }

            for (ix, value) in row.into_iter().enumerate() {
                // Cell separator
                if ix % num_cells == 0 {
                    write!(f, "| ")?;
                }
                // Value
                if let Some(value) = value {
                    write!(f, "{value:>value_pad$} ")?;
                } else {
                    write!(f, "{:>value_pad$} ", '.')?;
                }
            }
            writeln!(f, "|")?;
        }

        write!(f, "{sep_line}")
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for Sudoku {
    fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let unchecked = Sudoku::deserialize(deserializer)?;
        unchecked
            .validate_sudoku()
            .map_err(serde::de::Error::custom)
            .map(|_| unchecked)
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
impl std::fmt::Display for SolvedSudoku {
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
            if (ix % num_cells) == 0 {
                writeln!(f, "{sep_line}")?;
            }

            for (ix, value) in row.into_iter().enumerate() {
                // Cell separator
                if ix % num_cells == 0 {
                    write!(f, "| ")?;
                }
                // Value
                write!(f, "{value:>value_pad$} ")?;
            }
            writeln!(f, "|")?;
        }

        write!(f, "{sep_line}")
    }
}

/// A Simple sudoku value (may not be empty)
///
/// Limits grid size to 15x15 as it can only represent values up to 255 (16x16 grids require 256 to
/// be representable)
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SudokuValue(NonZeroU8);

impl SudokuValue {
    pub fn new(value: u8) -> Option<Self> {
        NonZeroU8::new(value).map(Self::from)
    }

    pub fn many(values: Vec<u8>) -> Vec<Option<Self>> {
        static_assertions::assert_eq_size!(u8, Option<SudokuValue>);

        // Safety: Niche optimization took place and Option<SudokuValue> is guaranteed to be 0 if
        // None and Some(NonZeroU8) if != 0, so Option<SudokuValue> covers all values of u8
        unsafe { std::mem::transmute(values) }
    }
}

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
    fn sudoku_2x2_bad_row() {
        let s = Sudoku::try_new(
            2,
            [1, 1, 3, 4, 3, 4, 1, 2, 4, 3, 2, 1, 2, 1, 4, 3]
                .into_iter()
                .map(NonZeroU8::new)
                .map(|val| val.map(Into::into))
                .collect(),
        );

        assert_eq!(s, Err(SudokuError::WrongValueSet { pos: (0, 0) }));
    }

    #[test]
    fn sudoku_2x2_bad_col() {
        let s = Sudoku::try_new(
            2,
            [1, 2, 3, 4, 4, 3, 1, 2, 4, 3, 2, 1, 2, 1, 4, 3]
                .into_iter()
                .map(NonZeroU8::new)
                .map(|val| val.map(Into::into))
                .collect(),
        );

        assert_eq!(s, Err(SudokuError::WrongValueSet { pos: (0, 1) }));
    }

    #[test]
    fn sudoku_2x2_bad_cell() {
        let s = Sudoku::try_new(
            2,
            [1, 2, 3, 4, 2, 1, 4, 3, 3, 4, 1, 2, 4, 3, 2, 1]
                .into_iter()
                .map(NonZeroU8::new)
                .map(|val| val.map(Into::into))
                .collect(),
        );

        assert_eq!(s, Err(SudokuError::WrongValueSet { pos: (0, 2) }));
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
            );
        }

        // Too big
        for grid_w in 16..=u8::MAX {
            let s = Sudoku::try_empty(grid_w.into());

            assert_eq!(
                s,
                Err(SudokuError::InvalidGridWidth {
                    grid_w: grid_w.into()
                })
            );
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
            );
        }
    }
}
