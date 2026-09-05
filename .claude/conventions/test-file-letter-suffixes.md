# Letter suffixes on split test files

When more than one unit test file covers the same subclause, end every file in that family with a letter: `test_simulator_subclause_11_04_11a.cpp`, `test_simulator_subclause_11_04_11b.cpp`, and so on. Reserve the unsuffixed name for a subclause that occupies exactly one file. A family of `…_11_04_11.cpp` plus `…_11_04_11a.cpp` is the shape to avoid, because the bare name reads as the whole of the subclause when it is really only the first part of it.

Letters run in content order, so `a` holds the cases that came first in the file the family was split from. When splitting a one-file subclause, rename the original to `a` rather than leaving it bare and starting the new file at `b`.

Each file is its own CMake target, so a rename means editing the `add_unit_test(...)` line in `test/CMakeLists.txt` to match. A target whose name no longer has a file behind it fails at configure time, not at build time.

## Check for the letter before writing the file

Run `ls test/src/unit/ | grep <subclause>` before choosing a suffix. The name one letter past the end of a family is easy to guess wrong, because an earlier split may already have claimed it, and writing over that file destroys the cases in it. The check costs one call, and it is the only thing standing between a split and silently deleted coverage.

Related: [overwritten-test-file](../incidents/overwritten-test-file.md) for the split that cost ten cases.
