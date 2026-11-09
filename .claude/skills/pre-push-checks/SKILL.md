---
name: pre-push-checks
description: Run the gates CI enforces over what the unpushed commits touch, before pushing them to main. Use before every push of a commit that changes C++ under src/ or test/, and whenever the user asks to check a change locally, build it, run its tests or see its coverage.
---

# Pre-push checks

`check.sh` in this directory runs, over the commits that `origin/main` lacks, the gates that sent pushes back red most often. It stops short of the full CI run and replaces none of it: it checks the files the commits touch and the unit tests named for them. The run after the push still gives the verdict over all of deltahdl, per `.claude/memories/verifying-through-ci.md`.

## Running it

Commit first, then run, from anywhere in the checkout:

```sh
.claude/skills/pre-push-checks/check.sh [extra_test_target ...]
```

It refuses to start while a tracked file has uncommitted changes, since what it checks has to be exactly what will be pushed. `PRE_PUSH_BASE=<commit>` checks the commits after that one in place of those after `origin/main`. The first run configures `build-check/`, a Debug tree built by Homebrew's `llvm@22` clang with coverage instrumentation, and builds the whole library, which takes several minutes; later runs rebuild only what changed. Run it in the background, per `.claude/memories/long-running-commands-in-the-background.md`.

Every touched file under `test/src/unit/` is built and run as its own target. Name as arguments any other test targets that reach the changed src code, such as the file holding the existing tests of a function a refactor moved. Coverage is read only from the tests that ran, so a changed line that only some other file's tests reach is reported until that file is named. To find that file, grep `test/src/unit/` for the construct the line handles; when no test reaches the line, write one.

## What it checks

- **Commit messages:** each subject is 72 characters or fewer, and each commit's `Closes`, `Refs` and `See` lines are printed so that a commit closing no issue shows.
- **Format and size:** every touched `.cpp` and `.h` file is `clang-format --style=google` clean and under 950 lines.
- **Registration:** every touched unit test file is listed by `add_unit_test` in `test/CMakeLists.txt` and declares a test, every touched src `.cpp` is listed in `src/CMakeLists.txt`, and no test name is declared twice anywhere under `test/src/unit/`.
- **Build and tests:** the library and the test targets build with `-Werror`, and every test in them passes.
- **Coverage:** every changed line under `src/` ran, and every branch outcome on a changed line was taken, with each condition of `&&` and `||` counted on its own, as `assert-coverage` counts them.
- **clang-tidy:** every touched src `.cpp` passes `etc/clang_tidy/src.yml`, and every touched unit test file passes `etc/clang_tidy/test_src_unit.yml`, all warnings as errors. These configurations carry the limits on statements, nesting, parameters and cognitive complexity, the naming rules and `misc-include-cleaner`, and they also check the repository headers each file includes.

## What it leaves to CI

The copy-paste detectors, the comment, suppression and citation scans, the sanitizer, gcc and Linux builds, the other unit tests, the e2e, integration and sv-tests runs, and the Python gates. A finding there is fixed as `.claude/memories/fixing-a-red-run.md` says.

## When it fails

Fix each problem it lists, amend the commit or add one, and run it again until it prints that every check passed; only then push. A finding that holds only on macOS, where CI's verdict on Linux differs, goes to CI: push, and if the run is green, add the case to this skill so the next run does not report it.
