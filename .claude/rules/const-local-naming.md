# Naming a const local

Name a `const` local `kCamelCase`, or drop the `const`. `etc/clang_tidy/test_src_unit.yml` and `etc/clang_tidy/src.yml` both set `readability-identifier-naming.LocalConstantCase: CamelCase` and `readability-identifier-naming.LocalConstantPrefix: k`, so `const std::string values = …` inside a function body is reported as "invalid case style for local constant 'values'" and fails a `clang-tidy-test-shard-*` or `clang-tidy-src` job.

The two names are both legal and the choice between them is what the local is for. A `const` that is carrying something — a value the rest of the body must not rebind, a table the reader is meant to read as fixed — is named `kCamelCase`. A `const` that is carrying nothing, which is most of the ones this rule catches, comes off, and the local keeps the `lower_case` name it had.

Removing the `const` is what both recorded breaches did. `fe6ce487e` failed `clang-tidy-test-shard-19` on one `const std::string w` in a randcase helper and `a6641b2ac` failed `clang-tidy-test-shard-13` on five in a VCD test file; in every one of the six the `const` was decoration on a local read once.

## Why it is worth a note

Because the shards were the only thing that said so. They report per file, one shard at a time, twenty minutes after a push, and a test author reading `.claude/CLAUDE.md` for what a test has to satisfy found the unique `Suite.Name`, the file-size cap and `ReportedError` there and nothing about naming. Two red runs in one session is what that cost.

The same pair covers `src/`, so the rule is not about tests. It is written from the test side because that is where it has been broken.

The configuration is the authority, not this file. `readability-identifier-naming` in those two YAML files carries entries for class constants, global constants, `constexpr` variables and enum constants as well, each with the same `k` prefix; read the file rather than this paragraph when a name is in question.

Related: [verifying-through-ci](verifying-through-ci.md), which is why the shard is where a naming breach surfaces at all.
