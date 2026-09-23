---
name: standard-names-listed-explicitly
description: "A gate's exemption for names IEEE 1800-2023 mandates lists every name explicitly and matches it exactly; a pattern is never used for a known, closed set, and this is not a decision to put to the user."
metadata: 
  node_type: memory
  type: feedback
---

# Names the standard mandates are listed explicitly and matched exactly

When a gate exempts names that IEEE 1800-2023 dictates, the exemption names every one of them and matches whole names. No wildcard, prefix pattern or substring stands in for a set the standard prints.

**Why:** Where the standard says how things must be named, an approximation will not do for names that are known and established. A pattern admits names the standard never printed, and the set is closed, so there is nothing for a pattern to do that a list does not do better. The choice is never open, so it is not a question for the user.

**How to apply:** Read the annex, list the names in the order printed, cite the pages, and match exactly — for `readability-identifier-naming` that means one parenthesized alternation, since the check wraps the value as `^…$` (see the comment above `FunctionIgnoredRegexp` in `etc/clang_tidy/src.yml`). Decide it and do it; do not file it as a decision. Related: [[lrm-source-of-truth]], [[solving-what-a-session-finds]].
