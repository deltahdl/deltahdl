# One declaration per fully-qualified test name

Declare each `Suite.Name` in one file only. A gtest case is identified by `Suite.Name`, and neither the compiler nor `gtest_discover_tests` objects when two files declare the same one. Each unit test source in `test/src/unit/` compiles into an executable of its own, and `gtest_discover_tests` registers every case into CTest under the bare `Suite.Name` — no binary, no path, nothing else to tell one from another. Two files declaring one name therefore produce two CTest tests called the same thing.

That costs two things. `ctest -R Suite.Name` and `--gtest_filter` both select every copy, so a case cannot be run on its own. And a failure report names the suite and the test but not the file, so a red run does not say which declaration broke.

The assert-no-duplicate-test-names job fails on any name declared more than once.

## Two files covering one rule is fine; two files sharing one name is not

Keep the overlap and change the name. An annex file covers a BNF production and a clause file covers the prose for the same feature, and a parser, preprocessor, elaborator or simulator file each covers a different stage of the pipeline over the same source. That overlap is deliberate and it is not what the check is about. The name is. Where two declarations stand, each name has to say which claim it makes.

Delete a declaration only when the two really do make one claim. In practice that means letter-suffix siblings covering the same clause, where one is a shallower restatement of the other. Across an annex and a clause file, prefer renaming: the coverage was put there on purpose.

## Naming the survivors

Derive the qualifier from what the body actually asserts, in the standard's own terms. §11.3.2 once had `Precedence.BitwiseOrHigherThanLogicalAnd` in two files: `a && b | c` in one and `a | b && c` in the other, the right-operand and left-operand cases of one precedence rule. The right-operand case became `BitwiseOrHigherThanLogicalAndOnRight` (`30aff9f54`). Where the difference is the pipeline stage rather than the claim, the repository already says `…Parses`, `…Elaborates` and `…ThroughPreprocessor`; use those rather than a new shape.

Write a comment above a renamed declaration saying what it covers and which sibling file carries the other case. That keeps the pair discoverable from either end.

## The check spans wrapped declarations

`clang-format` wraps a long declaration at the comma:

```cpp
TEST(SubroutineCallExprElaboration,
     ClassMethodRandomizeWithParenIdListAccepted) {
```

856 of the 28,798 declarations in the tree are shaped like that, so a line-at-a-time grep sees 97% of them and reports a clean run over the rest. The check joins each file's lines before matching.

Related: [test-file-letter-suffixes](../conventions/test-file-letter-suffixes.md) for the family a deletion case usually belongs to, and [verifying-through-ci](verifying-through-ci.md) for reading the result.
