# One declaration per fully-qualified test name

Declare each `Suite.Name` in one file only. The assert-no-duplicate-test-names job fails on any name declared more than once.

A gtest case is identified by `Suite.Name`, and neither the compiler nor `gtest_discover_tests` objects when two files declare the same one. Each unit test source in `test/src/unit/` compiles into an executable of its own, and every case is registered into CTest under the bare `Suite.Name` — no binary, no path, nothing else to tell one from another. So `ctest -R Suite.Name` and `--gtest_filter` select every copy, and a failure report names the suite and the test but not the file that broke.

## Two files covering one rule is fine; two files sharing one name is not

Keep the overlap and change the name. An annex file covers a BNF production and a clause file covers the prose for the same feature, and a parser, preprocessor, elaborator or simulator file each covers a different stage of the pipeline over the same source. That overlap is deliberate. Where two declarations stand, each name has to say which claim it makes.

Delete a declaration only when the two really do make one claim, which in practice means letter-suffix siblings where one is a shallower restatement of the other. Across an annex and a clause file, prefer renaming.

Derive the qualifier from what the body actually asserts, in the standard's own terms. Where the difference is the pipeline stage rather than the claim, the repository already says `…Parses`, `…Elaborates` and `…ThroughPreprocessor`; use those rather than a new shape. Write a comment above a renamed declaration saying what it covers and which sibling file carries the other case.

Related: [test-file-letter-suffixes](../conventions/test-file-letter-suffixes.md) for the family a deletion case usually belongs to, and [verifying-through-ci](verifying-through-ci.md) for reading the result.
