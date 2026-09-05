# CLAUDE.md

## Table of Contents

- [Conventions](#conventions)
  - [Commit messages](#commit-messages)
  - [Generated prompts and CI actions](#generated-prompts-and-ci-actions)
  - [Names](#names)
  - [Recording what a session learns](#recording-what-a-session-learns)
- [Rules](#rules)
  - [Commits and pushes](#commits-and-pushes)
  - [Formatting](#formatting)
  - [Reading the LRM](#reading-the-lrm)
  - [Scripts](#scripts)
  - [Source of truth](#source-of-truth)
  - [Tests](#tests)
  - [Verification](#verification)

## Conventions

Nothing enforces what is below. Each is a form this repository chose, where another choice would have served as well and the value is that everyone makes the same one.

### Commit messages

Longer: [closing-keyword-form](conventions/closing-keyword-form.md).

Write a close as `Closes #N` on its own line, one per issue, and a mention as `Refs #N` or `See #N`.

Describe a change to a module in that module's own terms: a docstring, comment, error message or commit message in module M should make sense to a reader who has never heard of anything that calls M.

Write the subject at the length that states the change, and leave the body unwrapped.

### Generated prompts and CI actions

Longer: [positive-prompts](conventions/positive-prompts.md), [composite-actions](conventions/composite-actions.md).

Write a CI mechanism as a composite action under `.github/actions/<name>/action.yml`, not as a shell script.

Phrase a prompt these scripts generate as the action wanted rather than the one forbidden.

### Names

Longer: [test-file-letter-suffixes](conventions/test-file-letter-suffixes.md).

When more than one unit test file covers a subclause, end every file in that family with a letter — `…_11_04_11a.cpp`, `…_11_04_11b.cpp` — and reserve the bare name for a subclause that fits in one file. Splitting a one-file subclause renames the original to `a`. Run `ls test/src/unit/` for the subclause first: an earlier split may already hold the letter, and writing over that file destroys its cases.

Give an inserted pipeline step a real position or a descriptive name, never "Step 0".

### Recording what a session learns

Write it down under `.claude/`, in the directory its kind belongs to: `rules/` for an instruction with a gate or a mechanism behind it, `conventions/` for a chosen form that a different choice would serve as well, `memories/` for a standing fact about the user or the project that the repository does not record on its own, and `references/` for lookup material. A rule or a convention also gets a section above or below, and a memory a line in `memories/MEMORY.md`.

A note earns its place by changing what a session would otherwise get wrong. What only explains why a rule is right belongs in the rule, in a clause.

## Rules

### Commits and pushes

Longer: [pushing-to-main](rules/pushing-to-main.md), [staging-explicit-paths](rules/staging-explicit-paths.md), [issue-closing-keywords](rules/issue-closing-keywords.md).

Commit straight to `main`. There is no pull-request cycle.

Stage each file by explicit path; `git add -A` and `git add .` sweep untracked scratch into history. Never name a removed path to `git add`, which then stages nothing at all. Read the index back with `git status --porcelain` before committing, and compare what it lists against what the change touched.

Reserve a closing keyword for the commit that finishes the issue. A keyword binds to a single `#N`, and brackets do not disable it, so a title naming an issue closes it on push.

Never suppress a CI run from a commit message. The `on:` triggers under `.github/workflows/` already decide which workflows a push needs.

### Formatting

Longer: [clang-format](rules/clang-format.md).

Run `clang-format -i --style=google` on every file a change touches. The style flag is required because the repository has no `.clang-format` file; without it clang-format reformats whole files under LLVM style and buries the real change.

Open every Markdown file with a top-level heading. markdownlint runs MD041 across `**/*.md`, dot-directories included.

### Reading the LRM

Longer: [reading-the-lrm](rules/reading-the-lrm.md), [oversized-tool-output](rules/oversized-tool-output.md), [locating-a-clause](references/locating-a-clause.md).

Read `~/LRM.pdf` with the Read tool, one page per call, waiting for each result before the next. Several page reads in one message exhaust a content-filter budget that does not recover for the rest of the turn, after which every tool result is suppressed. Extracting page text through `pypdf` does the same, and so can reading a very large source file in one call, so prefer a bounded window or a search.

### Scripts

Longer: [failing-loudly](rules/failing-loudly.md).

Crash the run when something goes wrong inside an orchestrator under `scripts/`, rather than skipping the item and carrying on. Record the human-resolvable state first if it helps, then raise or exit non-zero.

### Source of truth

Longer: [lrm-source-of-truth](rules/lrm-source-of-truth.md).

`~/LRM.pdf` (IEEE 1800-2023) decides what the code must do. Check any non-cosmetic change against the relevant clause. When a linter and the standard disagree, the standard wins; say so rather than quietly breaking conformance.

The standard also guides how code is structured. When grouping parameters into a struct, mirror the entities the standard defines for that feature.

### Tests

Longer: [test-driven-development](rules/test-driven-development.md), [unique-test-names](rules/unique-test-names.md).

Write the tests first, in the same commit as the code they cover. `.github/workflows/scripts.yml` runs `pytest --cov-fail-under=100` over the `unit/` directory of every Python script and library module. Test-first here means authoring order; the red-green observation belongs to CI.

Choose every input so that incorrect code would give a different answer from correct code. Some values make two quantities coincide — an offset and a count at zero, or an index and a storage offset in a vector declared `[N:0]` — and a test built on one passes whether the behaviour exists or not.

Give a fully-qualified name `Suite.Name` to one declaration only; CI fails on a repeated name. Two files covering one rule is fine and often deliberate, so rename the declaration to state its own claim rather than dropping the coverage.

A test that expects a source rejected names the report with `ReportedError` in `lib/cpp/test_helpers/helpers_reported_error.h`: a substring of the message, the line of the test's own source the report stands at, and the exact `Subclause("…")` text the emission site passes. Assertions that only ask whether something failed — `HasErrors()`, `has_errors`, `ParseOk`, `CompileOutcome::kFailed`, a `diags` count or emptiness check, `ErrorCount()`, a `LexWithDiag` error flag — pass when a different rule fired and when the source never reached the construct under test, and `FindDiag` and `r.diags.front()` select the wrong report as readily as the right one. Use `ReportedWarning` where the rule is enforced with a warning. Leave two kinds of site alone: one that varies only the construct under test while holding the rest of the source fixed, and one whose rule nothing reports, which needs an issue about the program instead. A test asserting a source was accepted is sound as it stands.

### Verification

Longer: [verifying-through-ci](rules/verifying-through-ci.md), [diagnosing-sv-tests-failures](rules/diagnosing-sv-tests-failures.md), [fetching-an-sv-tests-file](references/fetching-an-sv-tests-file.md).

CI is the source of truth. Make the edits, format, commit explicit paths, push to `main`, then read the run with `gh run list` and `gh run view`.

Never build locally, and never run any local tool that CI also runs — `clang-tidy`, the formatting check, the file-size cap, the suppression and configuration assertions, the test registration checks, the copy-paste detectors, and the Python gates in `.github/workflows/scripts.yml` are all CI jobs. Neither "it is not a build or a test" nor "it reproduces in a second" exempts a tool; the cost is the tokens spent reading its output, and CI is free.

Two things may be run locally. `clang-format`, because it rewrites files rather than judging them. And the simulator, built and run over a single sv-tests file that a run has already reported failing, because the CI log keeps only the first `:assert:` line that did not hold and drops the rest of a simulation's stdout. Read the log first: a file that fails by being rejected is already diagnosed there. Nothing else exempts a bug on the grounds that it only shows up while the simulator is running — read the code and the clause instead.

Some gates take their limits from a tracked file: a linter configuration, or a threshold written into the workflow. Check a change against those limits by reading that file.

Fix a red run in the session that finds it, whoever caused it. A change is unverified until the jobs that build and test have actually run, a conclusion of `failure` reads the same whether the change broke something or inherited a break, and a skipped job reports neither pass nor fail; `gh run view --log-failed` tells them apart. A pre-existing failure is a task, not a disposition.
