---
name: renaming-rather-than-deleting-a-duplicate-test
description: "Two files covering one rule is fine; resolve a duplicate gtest name by renaming the declaration, not by dropping coverage."
metadata:
  node_type: memory
  type: feedback
  originSessionId: e10149e7-3409-4014-9cb5-13a14e355d4b
  modified: 2026-11-21T02:50:48.155Z
---

# Renaming rather than deleting a duplicate test name

Keep the overlap and change the name when two declarations collide.

**Why:** An annex file covers a BNF production and a clause file covers the prose for the same feature, and a parser, preprocessor, elaborator or simulator file each covers a different stage of the pipeline over the same source. That overlap is deliberate. Deleting one to satisfy the `assert-no-duplicate-test-names` job drops real coverage to fix a naming problem.

**How to apply:** Derive the qualifier from what the body actually asserts, in the standard's own terms, so that each name says which claim it makes. Where the difference is the pipeline stage rather than the claim, the repository already says `…Parses`, `…Elaborates` and `…ThroughPreprocessor`; use those rather than a new shape. The commit message says which sibling file carries the other case, since the test file carries no comment ([no-comments-in-any-file](no-comments-in-any-file.md)). Delete a declaration only when the two really do make one claim, which in practice means letter-suffix siblings — see [test-file-letter-suffixes](test-file-letter-suffixes.md) — where one is a shallower restatement of the other. Across an annex and a clause file, prefer renaming.
