---
name: standard-names-listed-explicitly
description: "A gate's exemption for names IEEE 1800-2023 mandates lists every name explicitly and matches it exactly; a pattern is never used for a known, closed set, and this is not a decision to put to the user."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: b2f058fb-9712-46b0-abf4-2381afd5aea4
  modified: 2026-09-19T05:45:51.197Z
---

# Names the standard mandates are listed explicitly and matched exactly

When a gate exempts names that IEEE 1800-2023 dictates, the exemption names every one of them and matches whole names. No wildcard, prefix pattern or substring stands in for a set the standard prints. The user set this on 2026-09-19 after #3642 was carried through a `needs decision` label and a long exchange over whether `sv[A-Z].*` could stay in `FunctionIgnoredRegexp` for the DPI's 66 functions.

**Why:** In the user's words: if the standard says "you must name things this way" then we cannot use approximations for things that are known and established. A pattern admits names the standard never printed, and the set is closed, so there is nothing for a pattern to do that a list does not do better. The choice was never open, and asking was the wrong move.

**How to apply:** Read the annex, list the names in the order printed, cite the pages, and match exactly — for `readability-identifier-naming` that means one parenthesized alternation, since the check wraps the value as `^…$` (see the comment above `FunctionIgnoredRegexp` in `etc/clang_tidy/src.yml`). Decide it and do it; do not file it as a decision. Related: [[lrm-source-of-truth]], [[solving-what-a-session-finds]].
