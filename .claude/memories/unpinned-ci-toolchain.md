---
name: unpinned-ci-toolchain
description: CI floats every tool to its latest release; Actions tags stay at their major version.
metadata:
  type: project
---

# The unpinned CI toolchain

Nothing in CI is pinned; everything floats to latest, so CI runs the tool versions a current local install has, and a pinned clang-format cannot lag the local one and format differently.

Runner images float as `ubuntu-latest` and `macos-latest`, on `runs-on:` lines only. The job and artifact name strings such as `build-ubuntu-24-04-x86-64-clang` are identifiers that `needs:` and artifact references depend on, so those stay as labels. LLVM, clang, clang-tidy, clang-format, llvm-cov, llvm-profdata, g++ and gcc carry no version suffix. PMD resolves its latest release through the GitHub API into a step output with a dynamic cache key.

Latest means the latest release, not trunk. The unversioned apt.llvm.org repository — `deb http://apt.llvm.org/<codename>/ llvm-toolchain-<codename> main` — is trunk, and the highest clang it offers is an unreleased development build. Trunk makes the formatting gate unwinnable, because nightly output drifts and cannot be reproduced off the runner, and it destabilises clang-tidy. So `install-llvm` queries `api.github.com/repos/llvm/llvm-project/releases/latest`, derives the major version, and adds the stable branch repository `llvm-toolchain-<codename>-<major> main`, which follows releases automatically while staying reproducible.

GitHub Actions tags are the exception and stay at their major version (`@v5`, `@v4`). Floating within a major is the safe mechanism; unpinning to a moving ref is a supply-chain risk.

Related: [composite-actions](composite-actions.md) for the shape the mechanism is written in.
