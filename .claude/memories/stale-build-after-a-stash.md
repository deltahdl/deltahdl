---
name: stale-build-after-a-stash
description: A git stash round trip on the working tree leaves the incremental build in build/ stale often enough that a probe run after it cannot be trusted; build the comparison binary in a separate directory instead.
metadata:
  type: feedback
---

# A stash round trip leaves the build stale

To compare the behaviour of a change against the tree without it, build the unchanged binary somewhere other than `build/`: a scratch build directory configured from a `git worktree` of HEAD, or a copy of `build/src/deltahdl` taken before any source is touched. Never `git stash`, build, `git stash pop` and rebuild in `build/`, and never trust a probe run on `build/src/deltahdl` right after such a round trip.

**Why:** within one session, three probes run after a stash round trip in `build/` read a stale binary: a crash that a forced rebuild cured, an old count for a fixed defect, and a count off by one that sent a correct change to CI under suspicion. `make` decides by timestamps, and a stash and its pop rewrite source timestamps without regard to the object files between them, so an object compiled from the stashed state can stand newer than the restored source and not be rebuilt. The failures look exactly like real defects in the change.

**How to apply:** when a local probe of a change disagrees with what the change should do and a stash has touched the tree since the last clean build, touch every changed file, headers included, and rebuild before reading the result, or rebuild from nothing. A comparison against the unchanged tree is built from a worktree. See [[verifying-through-ci]]: CI's clean build is what decides.
