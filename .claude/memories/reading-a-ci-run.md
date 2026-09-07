---
name: reading-a-ci-run
description: Read a run with gh run list and gh run view; never push while a run is in flight, and compare runs over definite results.
metadata:
  type: feedback
---

# Reading a CI run

Read the result with `gh run view`, `gh run list` and `gh api repos/deltahdl/deltahdl/actions/jobs/<id>/logs`.

**Why:** CI is the source of truth for whether a change works — see [verifying-through-ci](verifying-through-ci.md) — so the reading is the verification, and doing it wrong leaves the change unverified while looking otherwise.

**How to apply:** Check `gh run list --limit 1` before pushing, because a push cancels a run that is in flight. Use `gh run view --log-failed` to get the file, line and check for each failure. Compare two runs over the tests that reported a definite `Passed` or `***…` result in both, never over failure counts or bare set differences, and confirm that every shard reached its CTest summary — a shard that died early reports fewer failures than one that finished. See [fixing-a-red-run](fixing-a-red-run.md) for what to do with what the run says.
