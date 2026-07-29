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

## Not every gating check has a number

The table above is the part of these files with numbers in it, which makes
it the part that gets checked. The rest of each file is a list of enabled
checks, and several of them fire on the *shape* of a piece of code with no
threshold to look up:

- `readability-simplify-boolean-expr`
- `misc-redundant-expression`
- `cppcoreguidelines-init-variables`
- `modernize-use-auto`, `modernize-use-nullptr`, `modernize-use-override`
- `performance-*`

A run was lost to the first of these. A guard written as

```cpp
return !(expr->elements.size() == 1 &&
         expr->elements[0]->kind == ExprKind::kReplicate);
```

is a negated conjunction, and the check requires DeMorgan's form:

```cpp
return expr->elements.size() != 1 ||
       expr->elements[0]->kind != ExprKind::kReplicate;
```

The two are the same predicate, so nothing about the standard is at stake
and there is no conflict to surface — it is purely a form the gate insists
on. That is what makes it easy to lose a run to: the 1000-line cap,
`clang-format` and both `pmd cpd` gates can all pass on a change that this
one rejects.

So when a change introduces a new predicate, a new local, or a new
overriding method, read the enabled-checks list of the relevant config as
well as the table. Both files are a file read away, and the section for
`src/` ends at `HeaderFilterRegex`.

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

## Nesting is counted from the function, not from the block

`NestingThreshold` is 4 in both configs, and it counts every enclosing
brace inside the function, not the depth of the construct being written.
A loop body nested in a `switch` case nested in a loop is already at four,
so adding one `for` inside it fails the gate — which is how
`Elaborator::ElaborateGenerateItems` lost run 30466727912 and the whole
matrix behind it.

The trap is that the added code looks flat where it is written. Two
sibling `for` loops stamping a value onto a vector read as one simple
step; what breaks the threshold is the three levels they were dropped
into. So the count to check is the one from the function's opening brace,
and the remedy is to give the innermost work its own function, as
`ElaborateGenerateBlockItem` now is.

Unlike cognitive complexity, this one is countable by eye before pushing:
open the function and count braces down to the line being added.
