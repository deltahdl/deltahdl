---
name: const-local-naming
description: Name a const local kCamelCase, or drop the const; clang-tidy's LocalConstantPrefix is the only thing that says so.
metadata:
  type: project
---

# Naming a const local

Name a `const` local `kCamelCase`, or drop the `const`.

**Why:** `etc/clang_tidy/test_src_unit.yml` and `etc/clang_tidy/src.yml` both set `readability-identifier-naming.LocalConstantCase: CamelCase` and `readability-identifier-naming.LocalConstantPrefix: k`, so `const std::string values = …` inside a function body is reported as "invalid case style for local constant 'values'" and fails a `clang-tidy-test-shard-*` or `clang-tidy-src` job. The shards were the only thing that said so: they report per file, one shard at a time, twenty minutes after a push. Two red runs in one session is what that cost.

**How to apply:** The two names are both legal and the choice between them is what the local is for. A `const` that is carrying something — a value the rest of the body must not rebind, a table the reader is meant to read as fixed — is named `kCamelCase`. A `const` that is carrying nothing, which is most of the ones this rule catches, comes off, and the local keeps the `lower_case` name it had. Removing the `const` is what both recorded breaches did: `fe6ce487e` failed `clang-tidy-test-shard-19` on one `const std::string w` in a randcase helper, and `a6641b2ac` failed `clang-tidy-test-shard-13` on five in a VCD test file; in every one of the six the `const` was decoration on a local read once. The same pair of configuration files covers `src/`, so this is not a test-only rule. Read the configuration rather than this file when a name is in question — it carries entries for class constants, global constants, `constexpr` variables and enum constants as well, each with the same `k` prefix. See [gate-limits-live-in-tracked-files](gate-limits-live-in-tracked-files.md).
