---
name: unpinned-ci-toolchain
description: CI floats every tool to its latest release; Actions tags stay at their major version.
metadata:
  node_type: memory
  type: project
  originSessionId: 9116bcc7-ba03-4fac-85c7-5b0966d82e64
  modified: 2026-10-26T11:52:09.143Z
---

# The unpinned CI toolchain

Nothing in CI is pinned; everything floats to latest, so CI runs the tool versions a current local install has, and a pinned clang-format cannot lag the local one and format differently.

Runner images float as `ubuntu-latest` and `macos-latest`, on `runs-on:` lines only. The job and artifact name strings such as `build-ubuntu-24-04-x86-64-clang` are identifiers that `needs:` and artifact references depend on, so those stay as labels. LLVM, clang, clang-tidy, clang-format, llvm-cov, llvm-profdata, g++ and gcc carry no version suffix. PMD resolves its latest release through the GitHub API into a step output with a dynamic cache key.

Latest means the latest release, not trunk. The unversioned apt.llvm.org repository — `deb http://apt.llvm.org/<codename>/ llvm-toolchain-<codename> main` — is trunk, and the highest clang it offers is an unreleased development build. Trunk makes the formatting gate unwinnable, because nightly output drifts and cannot be reproduced off the runner, and it destabilises clang-tidy. So `install-llvm` queries `api.github.com/repos/llvm/llvm-project/releases/latest`, derives the major version, and adds the stable branch repository `llvm-toolchain-<codename>-<major> main`, which follows releases automatically while staying reproducible.

The runner image floating moves the system headers too, and misc-include-cleaner's verdicts move with them while LLVM stays put: when `ubuntu-latest` went from 24.04 (noble) to 26.04 (resolute), the same clang-tidy 22.1.8 found 32 includes unused across files no commit had touched. When clang-tidy or include-cleaner goes red on untouched files, compare the `apt.llvm.org/<codename>` lines of the last passing run's log and the failing one's before anything else. A changed codename means the new verdicts are the ones to follow: check each finding against the file, then remove what it names in a push of its own.

GitHub Actions tags are the exception and stay at their major version (`@v5`, `@v4`). Floating within a major is the safe mechanism; unpinning to a moving ref is a supply-chain risk.

Related: [composite-actions](composite-actions.md) for the shape the mechanism is written in.
