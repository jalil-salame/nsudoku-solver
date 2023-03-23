use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use libnsudoku_solver::{
    solver::{self, Solver},
    Sudoku,
};

pub fn dfs(c: &mut Criterion) {
    let mut iterative = solver::IterativeDfs::default();
    let mut recursive = solver::RecursiveDfs::default();
    let mut group = c.benchmark_group("DFS: Empty Sudoku");

    let grid_w = 2;
    let sq_gw = grid_w * grid_w;
    let empty = Sudoku::empty(grid_w);

    group.bench_with_input(
        BenchmarkId::new(format!("Iterative {sq_gw}×{sq_gw} Sudoku"), sq_gw * sq_gw),
        &empty,
        |b, empty| b.iter(|| iterative.solve(empty.clone())),
    );
    group.bench_with_input(
        BenchmarkId::new(format!("Recursive {sq_gw}×{sq_gw} Sudoku"), sq_gw * sq_gw),
        &empty,
        |b, empty| b.iter(|| recursive.solve(empty.clone())),
    );

    group.finish();
}

criterion_group!(benches, dfs);
criterion_main!(benches);
