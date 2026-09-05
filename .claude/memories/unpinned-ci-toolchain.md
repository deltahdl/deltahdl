---
name: unpinned-ci-toolchain
description: CI floats every tool to latest, decided 2026-06-23; Actions tags stay at their major version.
metadata:
  type: project
---

# The unpinned CI toolchain

Nothing in CI is pinned; everything floats to latest. The decision was made on 2026-06-23, prompted by clang-format resolving to v19 in CI while the local install was v22. It landed on `main` in commits `240075952`, `b77615a7b` and `d95a32ef0`.

Runner images float: `ubuntu-24.04` to `ubuntu-latest` and `macos-26` to `macos-latest`, on `runs-on:` lines only. The job and artifact name strings such as `build-ubuntu-24-04-x86-64-clang` are identifiers that `needs:` and artifact references depend on, so those stay as labels. LLVM, clang, clang-tidy, clang-format, llvm-cov, llvm-profdata, g++ and gcc are no longer version-suffixed. PMD resolves its latest release through the GitHub API into a step output with a dynamic cache key.

One trap is worth remembering. The unversioned apt.llvm.org repository — `deb http://apt.llvm.org/<codename>/ llvm-toolchain-<codename> main` — is trunk, not stable, so picking the highest available clang selected 23, an unreleased development build. Trunk makes the formatting gate unwinnable, because nightly output drifts and cannot be reproduced off the runner, and it destabilises clang-tidy. The fix in `b77615a7b` queries `api.github.com/repos/llvm/llvm-project/releases/latest`, derives the major version, and adds the stable branch repository `llvm-toolchain-<codename>-<major> main`. That still follows releases automatically while staying reproducible.

GitHub Actions tags are the exception and stay at their major version (`@v5`, `@v4`). Floating within a major is the safe mechanism; unpinning to a moving ref is a supply-chain risk. This was flagged to the user and deliberately left pinned.

Related: [composite-actions](../conventions/composite-actions.md) for the shape the mechanism is written in.
