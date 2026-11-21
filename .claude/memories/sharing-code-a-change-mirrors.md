---
name: sharing-code-a-change-mirrors
description: "When a change gives two parallel pieces of code the same body, or writes a test that mirrors another's assertions, share it before pushing; the copy-paste jobs refuse a run of 100 identical tokens across src/ and across the tests."
metadata:
  node_type: memory
  type: feedback
  originSessionId: ef682c43-8cab-4c9d-8a68-d98c1351a7e5
  modified: 2026-11-21T02:52:08.928Z
---

# Sharing code a change mirrors

When a change brings two places in the tree to the same text, share it in the same commit, before pushing. This covers two scans, two handlers, or two tests that assert the same things.

**Why:** `copy-paste-src` and `copy-paste-test` in `.github/workflows/deltahdl.yml` run `pmd cpd --minimum-tokens 100` over `src/`, and over `test/src/` with `lib/cpp/`. Parallel code is where a fix is most often applied twice, such as the sequence and property port-list scans in src/parser. Once the fix makes the two bodies equal, the job fails, and the push that follows exists only to undo the copy. The same happens to a test written for one construct by copying its sibling's checks.

**How to apply:** Before staging, look for the counterpart of each function or test the change touched. For a scanner, that is its sequence or property twin. For a test, it is the test of the sibling clause. If the change leaves a run of about ten lines equal in both, move the body into one function both call. For tests, check through a different form, such as a summary string. The threshold is the `--minimum-tokens` value those jobs pass. The detectors run only in CI, so this look is the only check before the push ([verifying-through-ci](verifying-through-ci.md)).
