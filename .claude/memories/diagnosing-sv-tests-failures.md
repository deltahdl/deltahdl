---
name: diagnosing-sv-tests-failures
description: Root-cause a failing sv-tests file by running the binary on it, not by reading the source; predates the never-build-locally rule.
metadata:
  type: project
---

# Diagnosing sv-tests failures

To root-cause a failing sv-tests file, run the binary on that file. Do not reason about the failure from the source alone.

On 2026-07-01 reading the code produced two confident hypotheses in a row — scalar-versus-queue dispatch, then concat-init-not-lowered — and both were wrong. The actual causes only became visible from the binary's own output. These are mismatches between what a whole simulator run prints and what the file expects, which is exactly the case that makes local running inevitable, and the user authorised it.

Fetch the file with:

```sh
gh api repos/chipsalliance/sv-tests/contents/tests/chapter-N/<path>.sv \
  --jq .content | base64 -d
```

Then run it from an isolated Debug build directory; `ninja src/deltahdl` rebuilds incrementally. A file passes when each `:assert:` line reports equal values.
