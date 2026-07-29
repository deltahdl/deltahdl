# The clang-tidy thresholds a new signature has to clear

`clang-tidy` is a gating job. When `clang-tidy-src-shard-*` or
`clang-tidy-test-shard-*` fails, the whole unit-test matrix is skipped and
the push verifies nothing — the cost of tripping one of these is a lost
run, not a warning.

The numbers are tracked in the repository, so checking a change against
them costs a file read rather than a local analyser sweep.
`etc/clang_tidy/src.yml` governs `src/` and `etc/clang_tidy/test_src_unit.yml`
governs `test/src/unit/`:

| Limit | `src/` | `test/src/unit/` |
| --- | --- | --- |
| `readability-function-cognitive-complexity.Threshold` | 15 | 15 |
| `readability-function-size.ParameterThreshold` | 5 | 5 |
| `readability-function-size.NestingThreshold` | 4 | 4 |
| `readability-function-size.StatementThreshold` | 50 | 100 |
| `readability-function-size.LineThreshold` | 200 | 300 |

## Adding a parameter is the easy one to miss

Cognitive complexity is the limit that gets talked about, but the
parameter count is the one that catches a mechanical change. Threading a
new argument — a scope, a context, a flag — through a handful of existing
functions is exactly the kind of edit that reads as safe and pushes a
five-parameter function to six. Count the parameters of every signature a
change touches before pushing, the same way the 1000-line cap is checked.

Grouping the excess into a struct is the expected remedy, and
[lrm-source-of-truth](lrm-source-of-truth.md) decides its shape: mirror the
entity the standard defines for the feature rather than inventing a
container of convenience. `EnumMemberDeclCtx` in
`src/elaborator/elaborator_typedef.cpp` groups the four things that
describe *where* an enumeration's named constants are declared, because
§6.19 declares them in the enclosing scope rather than in the type,
leaving the enumeration's own members and width as direct parameters.

## A const local is a constant, and is named like one

`readability-identifier-naming` sets `LocalConstantPrefix: k` with
`LocalConstantCase: CamelCase`, so `const ScopeMap no_scope;` is an error
and `const ScopeMap kNoScope;` is not. A plain local variable stays
`lower_case`.

That makes the `const` a naming decision rather than a free bit of rigour.
Where a local exists only to have its address or reference passed to
something taking a `const&`, dropping the `const` keeps the descriptive
`lower_case` name and reads as the value it is; where a local really is a
named constant of the function, spell it `kLikeThis`. Either is fine, but
they are not interchangeable, and adding `const` to a `lower_case` local
turns a clean file into a gating failure.
