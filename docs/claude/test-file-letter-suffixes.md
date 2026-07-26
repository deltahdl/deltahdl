# Letter suffixes on split test files

When more than one unit test file covers the same clause, every file in
that family ends in a letter: `test_simulator_clause_11_04_11a.cpp`,
`test_simulator_clause_11_04_11b.cpp`, and so on. The unsuffixed name is
for a clause that occupies exactly one file. A family of `…_11_04_11.cpp`
plus `…_11_04_11a.cpp` is the shape to avoid — the bare name reads as the
whole of the clause when it is really only the first part of it.

Letters run in content order, so `a` holds the cases that came first in
the file the family was split from. Splitting a one-file clause therefore
renames the original to `a` rather than leaving it bare and starting the
new file at `b`.

Each file is its own CMake target, so a rename means editing the
`add_unit_test(...)` line in `test/CMakeLists.txt` to match. A target
whose name no longer has a file behind it fails at configure time, not
at build time.

## Check for the letter before writing the file

The name one letter past the end of a family is easy to guess wrong,
because an earlier split may already have claimed it. On 2026-07-26 a
split of `test_parser_annex_a_09_03.cpp` wrote its second half straight
to `test_parser_annex_a_09_03a.cpp` with a `>` redirect. That file
already existed — commit `c30f5c7ce` had created it — and the redirect
destroyed the ten test cases in it. Nothing caught this until CMake
refused the duplicate `add_unit_test` line, and by then the loss was
committed.

`ls test/src/unit/ | grep <clause>` before choosing a suffix. It costs
one call and it is the only thing standing between a split and silently
deleted coverage.

Related: [file-size-cap](file-size-cap.md) for why a test file gets split
in the first place.
