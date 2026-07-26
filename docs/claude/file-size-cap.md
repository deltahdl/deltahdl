# The 1000-line file cap

CI fails any `.cpp` or `.h` under `src/` or `test/` that exceeds 1000
lines. Splitting a file into cohesive units is the sanctioned remedy —
commit `c30f5c7ce` is the precedent. Do not compress or obfuscate to get
under the cap, and do not avoid a needed change out of fear of the line
count.

Copy the include block into the new file verbatim. `misc-include-cleaner`
is not enabled — it appears nowhere in `etc/clang_tidy/src.yml`,
`etc/clang_tidy/test_src_unit.yml` or `.github/workflows/deltahdl.yml` — so
an over-broad include set carried across from the parent costs nothing,
while pruning includes by hand risks breaking the build.

`src/elaborator/elaborator.h` is a special case: it is one monolithic
`class Elaborator` with nothing else at file scope. A class body cannot be
split across files, so when it reaches the cap the remedy is extraction,
not splitting — pull a cohesive family of methods into its own class and
file. The bodies touch many private members, so the helper needs friend
access or an `Elaborator&`, and the moved methods stop being members.

On 2026-06-28 that header sat at exactly 1000 lines and adding
`ValidateHierRefUndeclaredMember` pushed it to 1004. The stopgap was to
fold the new §23.6 check into the existing
`ValidateHierRefToImportedName`, which has the same signature and walk, so
only one declaration was added. When it next overflows, extract the
scope-rule validators — `ValidateUnresolvedReferences`,
`ValidateHierRef*`, `CheckHierRefUndeclaredMember`, `IsDeclaredNameForRhs`
and `IsNameInModuleScope` — into a `ScopeRuleValidator` for durable
headroom, rather than trimming blank lines again.
