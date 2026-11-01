---
name: reading-a-ci-run
description: Read a run with gh run list and gh run view; never push while a run is in flight, and compare runs over definite results.
metadata:
  type: feedback
---

# Reading a CI run

Read the result with `gh run view`, `gh run list` and `gh api repos/deltahdl/deltahdl/actions/jobs/<id>/logs`.

**Why:** CI is the source of truth for whether a change works — see [verifying-through-ci](verifying-through-ci.md) — so the reading is the verification, and doing it wrong leaves the change unverified while looking otherwise.

**How to apply:** Check `gh run list --limit 1` before pushing, because a push cancels a run that is in flight. A run has finished only when `gh run view <id> --json status` says `completed`: until a matrix expands, the job list carries it as a single `…-shard-${{ matrix.shard }}` placeholder, so a script that polls job statuses can call a run clean after the lint jobs, while its builds and tests have not yet started. Use `gh run view --log-failed` to get the file, line and check for each failure, and read it only once the run has completed, listing every job that did not succeed: a watcher that stops at the first red job reports a clang-tidy finding and hides failed test shards behind it, so a fix for the one it named is pushed onto a run that stays red. Compare two runs over the tests that reported a definite `Passed` or `***…` result in both, never over failure counts or bare set differences, and confirm that every shard reached its CTest summary — a shard that died early reports fewer failures than one that finished. See [fixing-a-red-run](fixing-a-red-run.md) for what to do with what the run says.
