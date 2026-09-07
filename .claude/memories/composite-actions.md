---
name: composite-actions
description: Write a CI mechanism as a composite action under .github/actions/<name>/action.yml, not as a shell script.
metadata:
  type: feedback
---

# Composite actions over shell scripts

Write a CI mechanism as a composite action, not as a shell script.

**Why:** The user rejected a raw `scripts/ci/*.sh` attempt in favour of a composite action — see [unpinned-ci-toolchain](unpinned-ci-toolchain.md) for the change that occasioned the pattern. Nothing enforces the choice; a shell script would work.

**How to apply:** The house pattern is `.github/actions/<name>/action.yml` with `using: composite` and alphabetical keys, as in the sibling repository at `~/Git/10U-Labs/10ulabs.com`. `install-llvm` and `install-gcc` exist here. A job uses the action and then has a small `run:` step for ccache, pip or pmd, since a `uses:` step cannot also `run:`.
