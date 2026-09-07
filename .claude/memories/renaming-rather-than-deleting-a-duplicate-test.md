---
name: renaming-rather-than-deleting-a-duplicate-test
description: Two files covering one rule is fine; resolve a duplicate gtest name by renaming the declaration, not by dropping coverage.
metadata:
  type: feedback
---

# Renaming rather than deleting a duplicate test name

Keep the overlap and change the name when two declarations collide.

**Why:** An annex file covers a BNF production and a clause file covers the prose for the same feature, and a parser, preprocessor, elaborator or simulator file each covers a different stage of the pipeline over the same source. That overlap is deliberate. Deleting one to satisfy [unique-test-names](unique-test-names.md) drops real coverage to fix a naming problem.

**How to apply:** Derive the qualifier from what the body actually asserts, in the standard's own terms, so that each name says which claim it makes. Where the difference is the pipeline stage rather than the claim, the repository already says `…Parses`, `…Elaborates` and `…ThroughPreprocessor`; use those rather than a new shape. Write a comment above a renamed declaration saying what it covers and which sibling file carries the other case. Delete a declaration only when the two really do make one claim, which in practice means letter-suffix siblings — see [test-file-letter-suffixes](test-file-letter-suffixes.md) — where one is a shallower restatement of the other. Across an annex and a clause file, prefer renaming.
