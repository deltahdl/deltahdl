---
name: composite-actions
description: "Write a CI mechanism as a composite action under .github/actions/<name>/action.yml, not as a shell script."
metadata:
  node_type: memory
  type: feedback
  originSessionId: e10149e7-3409-4014-9cb5-13a14e355d4b
  modified: 2026-11-21T02:52:10.078Z
---

# Composite actions over shell scripts

Write a CI mechanism as a composite action, not as a shell script.

**Why:** It is the user's house pattern, shared with the sibling repository at `~/Git/10U-Labs/10ulabs.com`. Nothing enforces the choice; a shell script would work.

**How to apply:** The house pattern is `.github/actions/<name>/action.yml` with `using: composite` and alphabetical keys. `install-llvm` and `install-gcc` exist here; [ci-toolchain-versions](ci-toolchain-versions.md) says which versions they install. A job uses the action and then has a small `run:` step for ccache, pip or pmd, since a `uses:` step cannot also `run:`.
