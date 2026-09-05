# CLAUDE.md

## Table of Contents

- [Overview](#overview)
- [Rules](#rules)
  - [Commits and pushes](#commits-and-pushes)
  - [Formatting](#formatting)
  - [Reading the LRM](#reading-the-lrm)
  - [Source of truth](#source-of-truth)
  - [Tests](#tests)
  - [Verification](#verification)

## Overview

deltahdl is a SystemVerilog simulator and elaborator pursuing IEEE 1800-2023 conformance. This file holds the standing conventions for working in this repository. Each section links the longer write-up behind it, one note per topic under `.claude/rules/`. Record a convention learned in a session the same way: a section here and a note there.

## Rules

### Commits and pushes

Longer: [pushing-to-main](rules/pushing-to-main.md), [staging-explicit-paths](rules/staging-explicit-paths.md), [issue-closing-keywords](rules/issue-closing-keywords.md).

Commit straight to `main`. There is no pull-request cycle, so CI is the only review buffer there is.

Stage each file by explicit path. `git add -A` and `git add .` sweep untracked scratch directories into history. Never name a removed path to `git add`, which stages none of its paths when one of them matches nothing on disk. Read the index back with `git status --porcelain` before committing.

`Closes #N`, `Fixes #N` and their variants close the issue the moment the commit lands, brackets or not. Write the closing form as `Closes #N`, one per line: a keyword binds to a single `#N`, so a comma-separated list closes only its first issue. Write `Refs #N` or `See #N` when the commit only mentions an issue.

Never suppress a CI run from a commit message. Let the `on:` triggers under `.github/workflows/` decide which workflows a push needs; they watch paths, and they are already correct about it. A push that changes nothing a workflow watches starts no run, and a push that does change something watched is a push whose run is wanted.

Describe a change to a shared module in that module's own terms. A docstring, comment, error message or commit message in module M should make sense to a reader who has never heard of anything that calls M.

Write the commit subject at the length that states the change, and leave the body unwrapped. Nothing measures the width of a commit message, and the shorter word chosen to fit a column is paid for out of the accuracy the message exists to carry.

### Formatting

Longer: [clang-format](rules/clang-format.md).

Run `clang-format -i --style=google` on every file a change touches. It is the one tool to run locally over what CI would otherwise judge, and it is allowed because it rewrites files rather than judging them: running it produces the bytes that get committed, so it is part of authoring a change rather than part of checking one. The style flag is required because the repository has no `.clang-format` file. Without the flag, clang-format falls back to the LLVM default, reformats whole files and buries the real change.

### Reading the LRM

Longer: [reading-the-lrm](rules/reading-the-lrm.md), [oversized-tool-output](rules/oversized-tool-output.md).

Read `~/LRM.pdf` with the Read tool, one page per call, and wait for each result before issuing the next. Several page reads in one message exhaust a content-filter budget that does not recover for the rest of the turn, after which every tool result is suppressed. Extracting page text through `pypdf` does the same, and reading a very large source file in one call can do it too, so prefer a bounded window or a search.

Printed page number plus one gives the PDF page. [locating-a-clause](rules/locating-a-clause.md) carries a snippet that resolves a clause to a page from the bookmarks without touching page content.

### Source of truth

Longer: [lrm-source-of-truth](rules/lrm-source-of-truth.md).

`~/LRM.pdf` (IEEE 1800-2023) decides what the code must do. Check any non-cosmetic change against the relevant clause, and make the code conform to the standard rather than to a linter. When a linter and the standard disagree, the standard wins. Say so rather than quietly breaking conformance.

The standard also guides how code is structured. When grouping parameters into a struct, mirror the entities the standard defines for that feature rather than inventing a container of convenience.

### Tests

Longer: [test-driven-development](rules/test-driven-development.md), [test-file-letter-suffixes](rules/test-file-letter-suffixes.md), [unique-test-names](rules/unique-test-names.md).

Write the tests first, in the same commit as the code they cover. `.github/workflows/scripts.yml` runs `pytest --cov-fail-under=100` over the `unit/` directory of every Python script and library module, so production code without matching unit tests fails on push. Test-first here means authoring order; the red-green observation belongs to CI.

Choose every input so that incorrect code would give a different answer from correct code. Some values make two quantities coincide, such as an offset and a count at zero, or a position and its name in a range that starts where counting starts. For such a value, code that confuses the two returns the right answer, so every test built on it passes whether the behaviour exists or not. §11.5.1 rules that a declaration decides which bit an index reaches, and that rule went untested for exactly this reason: every test declared its vectors `[N:0]`, where the index and the storage offset are the same number, and two elaborator paths computed offsets where indices were required without one test noticing.

When more than one unit test file covers the same subclause, end every file in that family with a letter — `…_11_04_11a.cpp`, `…_11_04_11b.cpp` — and reserve the bare name for a subclause that fits in one file. Splitting a one-file subclause renames the original to `a`. Run `ls test/src/unit/` for the subclause before choosing a suffix: an earlier split may already hold the letter, and writing over that file destroys its cases.

Give a fully-qualified name `Suite.Name` to one declaration only. Each unit test source builds its own executable, and `gtest_discover_tests` registers each case into CTest under the bare name. Two files declaring one name therefore give two CTest tests called the same thing, and neither `ctest -R` nor a failure report can tell them apart. Two files covering one rule is fine and often deliberate: an annex file for the BNF production beside a subclause file for the prose, or a parser file beside a preprocessor one. The shared name is what breaks, so give each declaration a name stating its own claim rather than dropping the coverage. CI fails on a repeated name.

A test that expects a source rejected names the report rather than the count, with one call to `ReportedError` in `lib/cpp/test_helpers/helpers_reported_error.h`. It names three things: a substring of the message, the line of the test's own source the report stands at, and the exact `Subclause("…")` text the emission site passes. `EXPECT_TRUE(f.diag.HasErrors())`, `EXPECT_TRUE(f.has_errors)`, `EXPECT_FALSE(ParseOk(...))`, `EXPECT_EQ(..., CompileOutcome::kFailed)`, `ASSERT_EQ(r.diags.size(), 1u)`, `ASSERT_FALSE(r.diags.empty())`, `EXPECT_EQ(f.diag.ErrorCount(), 1U)` and `EXPECT_TRUE(errors)` off an `auto [tokens, errors] = LexWithDiag(…)` binding are each satisfied by any rejection, so a test written for one rule passes when a different rule fired and passes when the source never reached the construct under test. A count is worse than the boolean rather than better: it states how many reports a run made and nothing about which rule any of them enforced, and it goes red when a second report is added for an unrelated reason. `FindDiag` selects a report by its message alone and matches a warning as readily as an error, and `r.diags.front()` is the wrong report to read when a source is rejected twice, so a body reading either names the report through `ReportedError` instead. Where the rule is one the program enforces with a warning, `ReportedWarning` in the same header answers the same three questions. Two kinds of site are not converted: one that varies only the construct under test while holding the rest of the source fixed, where a rejection is already attributable, and one whose rule nothing reports, which needs an issue about the program instead. A test asserting a source was accepted is sound as it stands, since there is no report to name, and so is one that reports the diagnostic itself and reads it back.

### Verification

Longer: [verifying-through-ci](rules/verifying-through-ci.md).

CI is the source of truth for build and test results. Make the edits, format, commit explicit paths, push to `main`, then read the run with `gh run list` and `gh run view`.

Never build locally, and never run any local tool that CI also runs. Outside the sv-tests case below, nothing exempts a bug on the grounds that it only shows up while the simulator is running. Find a coroutine, scheduler or event-watcher bug by reading the code and the LRM clause, not by reading a local print. When a defect really does hide in run-time state, read more closely rather than build.

There are two exceptions. `clang-format` rewrites files rather than judging them, so running it is how the committed bytes come to exist; see Formatting above. And the simulator may be built and run over a single sv-tests file that a run has already reported failing, because the CI log carries every rejection but drops the rest of a simulation's stdout, keeping only the first `:assert:` line that did not hold. Read the log before building: a file that fails by being rejected is already diagnosed there.

Every gate is covered by this, not just the build and the tests. `clang-tidy`, the formatting check, the file-size cap, the assertions about suppressions and configuration files, the unit test registration checks and the copy-paste detectors are CI jobs like any other, so verify a lint sweep by pushing and reading `gh run view --log-failed`. Neither "it is not a build or a test" nor "it reproduces in a second" exempts a tool. The cost of running one locally is the tokens spent reading its output, and CI is free.

Some gates take their limits from a file the repository tracks: a linter configuration, or a threshold written into the workflow that runs the tool. Check a change against those limits by reading that file. That is what makes running the tool unnecessary rather than merely forbidden.

The Python gates all run in `.github/workflows/scripts.yml`: pytest, the coverage gate, pylint, `mypy --strict`, the one-assert-per-test check and jscpd. Push and read them there.

Fix a red run in the session that finds it, whoever caused it. A gate that scans the whole tree rather than the diff indicts whoever pushes next by design, so repair its breach in the same session instead of leaving a note about it for somebody else. A change is unverified until the jobs that build and test have actually run. A conclusion of `failure` reads the same whether the change broke something or inherited a break, and a skipped job reports neither pass nor fail. Read the failed log to tell those apart. A pre-existing failure is a task, not a disposition.
