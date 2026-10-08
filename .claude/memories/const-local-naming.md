---
name: const-local-naming
description: "Name a const local kCamelCase, or drop the const; clang-tidy's LocalConstantPrefix is the only thing that says so."
metadata:
  node_type: memory
  type: project
  originSessionId: 0ce081b6-fd14-4da5-87da-08ca53aae436
  modified: 2026-10-08T14:01:25.137Z
---

# Naming a const local

Name a `const` local `kCamelCase`, or drop the `const`.

**Why:** `etc/clang_tidy/test_src_unit.yml` and `etc/clang_tidy/src.yml` both set `readability-identifier-naming.LocalConstantCase: CamelCase` and `readability-identifier-naming.LocalConstantPrefix: k`, so `const std::string values = …` inside a function body is reported as "invalid case style for local constant 'values'" and fails a `clang-tidy-test-shard-*` or `clang-tidy-src-shard-*` job. The shards are the only thing that says so: they report per file, one shard at a time, twenty minutes after a push.

**How to apply:** The two names are both legal and the choice between them is what the local is for. A `const` that is carrying something — a value the rest of the body must not rebind, a table the reader is meant to read as fixed — is named `kCamelCase`. A `const` that is carrying nothing, which is most of the ones this rule catches, comes off, and the local keeps the `lower_case` name it had. The same pair of configuration files covers `src/`, so this is not a test-only rule. A `const` reference is not a local constant to the check: `const VpiObject& kElement = …` fails as "invalid case style for variable", so a reference takes the plain `lower_case` name whatever it binds. Read the configuration rather than this file when a name is in question — it carries entries for class constants, global constants, `constexpr` variables and enum constants as well, each with the same `k` prefix. See [gate-limits-live-in-tracked-files](gate-limits-live-in-tracked-files.md).
