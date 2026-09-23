---
name: composite-actions
description: Write a CI mechanism as a composite action under .github/actions/<name>/action.yml, not as a shell script.
metadata:
  type: feedback
---

# Composite actions over shell scripts

Write a CI mechanism as a composite action, not as a shell script.

**Why:** It is the user's house pattern, shared with the sibling repository at `~/Git/10U-Labs/10ulabs.com`. Nothing enforces the choice; a shell script would work.

**How to apply:** The house pattern is `.github/actions/<name>/action.yml` with `using: composite` and alphabetical keys. `install-llvm` and `install-gcc` exist here; [unpinned-ci-toolchain](unpinned-ci-toolchain.md) says what they install. A job uses the action and then has a small `run:` step for ccache, pip or pmd, since a `uses:` step cannot also `run:`.
