---
name: verifying-through-ci
description: "Nothing is built or run locally: no build, no unit test, no probe through the deltahdl binary and no pre-push-checks; a change is pushed and CI's run gives the verdict."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 84445ccd-f1b9-420f-afbd-5b1a412da9aa
  modified: 2026-11-26T02:22:09.966Z
---

# Verifying through CI

Nothing is compiled or run locally. That means no build in `build-check/` or anywhere else, no unit test binary, no probe of a design through the `deltahdl` binary, and no `.claude/skills/pre-push-checks/check.sh`, which builds. A change is committed and pushed, and the CI run is the verdict on all of it: the unit tests, coverage of changed lines, clang-tidy, the sanitizer and gcc builds, the copy-paste detectors, and the e2e, integration and sv-tests runs.

**Why:** The user does not want anything built on the local machine. A local build holds the session for minutes to hours, and a local tree can drift from CI's setup unnoticed. When `build-check/` was reconfigured with the system compiler and no coverage flags, every local check after that reported nothing true.

**How to apply:**

- **Before a push,** check by reading, not running:
  - trace the code each new test reaches, and the reason it fails without the fix;
  - format changed C++ with `clang-format`, which compiles nothing;
  - keep files at or under 1000 lines;
  - register new test files in `test/CMakeLists.txt`;
  - keep the commit subject to 72 characters or fewer and each body paragraph on one line;
  - stay within the clang-tidy limits the touched code must meet.
- **A src change of any size** is pushed once traced through the code, even though CI is the first place it compiles; a red run it causes, a compile error included, is fixed in a push of its own. The user chose this over a local compile-only check.
- **After the push,** watch every run, per [watching-a-ci-run](watching-a-ci-run.md), read it, per [reading-a-ci-run](reading-a-ci-run.md), and fix a red run, per [fixing-a-red-run](fixing-a-red-run.md).
- **Coverage** of changed src lines is read from CI's coverage report, not from a local profile.
- Running Python tests with `pytest` compiles nothing and stays allowed.
