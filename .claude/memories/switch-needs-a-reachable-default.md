---
name: switch-needs-a-reachable-default
description: A switch naming every enumerator and no default leaves an implicit default llvm-cov counts as a missed branch; make one real case the default.
metadata:
  node_type: memory
  type: feedback
  originSessionId: dbb14fe5-4f12-40b5-98ca-0948dad60b8a
  modified: 2026-10-12T06:17:37.181Z
---

A `switch` over an `enum class` that writes a `case` for every enumerator and no `default` still has an implicit default branch, and llvm-cov counts it: no input reaches it, so it is one missed branch even with every line run. Write one enumerator's case as `default:` instead.

**Why:** the coverage TOTAL of missed branches may not rise above its baseline, and this miss shows only as a branch count (every line covered, one branch not), which is easy to misread as a gap in the tests.

**How to apply:** when a new file's coverage row reads 100% lines and one branch short, look for a switch without a default before writing more tests. Related: [[braced-case-closing-brace-is-a-line]].
