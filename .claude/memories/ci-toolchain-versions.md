---
name: ci-toolchain-versions
description: "CI's LLVM major is the default written in install-llvm and moves only in a commit of its own; jobs whose names state a platform pin that runner image; everything else floats to its latest release, and Actions tags stay at their major version."
metadata:
  node_type: memory
  type: project
  originSessionId: e10149e7-3409-4014-9cb5-13a14e355d4b
  modified: 2026-11-21T02:51:26.617Z
---

# Which CI tool versions are pinned

**LLVM.** `.github/actions/install-llvm/action.yml` installs the major its `major` input defaults to, a number written in that file. clang-format and clang-tidy judge the whole tree rather than a diff, so a new release re-judges code no commit touched; raising the default is therefore a commit of its own, carrying whatever the tree owes the new release. Passed empty, the input discovers the newest stable major through the GitHub releases API and installs it from that major's stable apt.llvm.org repository. The unversioned apt.llvm.org repository is trunk, whose output drifts nightly and cannot be reproduced off the runner, so it is never used. A job that consumes another job's compiled objects passes that job's `major` output, so both compile with the same release. Locally, the match for CI is Homebrew's `llvm@<major>` of that same major, as `pre-push-checks` uses it; the plain `llvm` formula is the newest release and can be ahead of CI.

**Runner images.** A job whose name states a platform, such as `build-ubuntu-24-04-x86-64-clang` or `unit-test-macos-26-arm64-clang`, runs on exactly that image, so its name stays true. Every other job runs on `ubuntu-latest`. A floating image moves the system headers, and misc-include-cleaner's verdicts move with them while LLVM stays put. When clang-tidy or include-cleaner goes red on files no commit touched, compare the `apt.llvm.org/<codename>` lines of the last passing run's log and the failing one's first. A changed codename means the new verdicts are the ones to follow: check each finding against the file, then remove what it names in a push of its own.

**Everything else** floats to its latest release: g++ and gcc carry no version suffix, and PMD and GoogleTest resolve their latest release through the GitHub API at run time.

**Actions tags** stay at their major version (`@v5`, `@v4`). Floating within a major is the safe mechanism; a moving ref such as a branch is a supply-chain risk.
