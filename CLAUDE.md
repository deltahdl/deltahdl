# Working in deltahdl

deltahdl is a SystemVerilog simulator and elaborator pursuing IEEE 1800-2023 conformance. This file holds the standing conventions for working in this repository. Each section links the longer write-up behind it, one note per topic under `docs/claude/`, and [docs/claude/README.md](docs/claude/README.md) indexes them all. Record a convention learned in a session the same way: a section here and a note there. Do not keep it in a session's own memory, which travels with one machine and is reviewed by nobody ([where-notes-live](docs/claude/where-notes-live.md)).

## Source of truth

`~/LRM.pdf` (IEEE 1800-2023) decides what the code must do. Check any non-cosmetic change against the relevant clause, and make the code conform to the standard rather than to a linter. When a linter and the standard disagree, the standard wins. Say so rather than quietly breaking conformance.

The standard also guides how code is structured. When grouping parameters into a struct, mirror the entities the standard defines for that feature rather than inventing a container of convenience.

Longer: [lrm-source-of-truth](docs/claude/lrm-source-of-truth.md).

## Verification

CI is the source of truth for build and test results. Make the edits, format, commit explicit paths, push to `main`, then read the run with `gh run list` and `gh run view`.

Never build locally, and never run any local tool that CI also runs. Nothing exempts a bug on the grounds that it only shows up while the simulator is running. Find a coroutine, scheduler or event-watcher bug by reading the code and the LRM clause, not by reading a local print. When a defect really does hide in run-time state, read more closely rather than build.

`clang-format` is the single exception, because it rewrites files rather than judging them. See Formatting below.

Every gate is covered by this, not just the build and the tests. `clang-tidy`, the file-size cap, the `static-analysis` checks and the copy-paste detectors are CI jobs like any other, so verify a lint sweep by pushing and reading `gh run view --log-failed`. Neither "it is not a build or a test" nor "it reproduces in a second" exempts a tool. The cost of running one locally is the tokens spent reading its output, and CI is free.

Some gates take their limits from a file the repository tracks: a linter configuration, or a threshold written into the workflow that runs the tool. Check a change against those limits by reading that file. That is what makes running the tool unnecessary rather than merely forbidden.

The Python gates all run in `.github/workflows/scripts.yml`: pytest, the coverage gate, pylint, `mypy --strict`, the one-assert-per-test check and jscpd. Push and read them there.

Fix a red run in the session that finds it, whoever caused it. A gate that scans the whole tree rather than the diff indicts whoever pushes next by design, so repair its breach in the same session instead of leaving a note about it for somebody else. A change is unverified until the jobs that build and test have actually run. A conclusion of `failure` reads the same whether the change broke something or inherited a break, and a skipped job reports neither pass nor fail. Read the failed log to tell those apart. A pre-existing failure is a task, not a disposition.

Longer: [verifying-through-ci](docs/claude/verifying-through-ci.md), [inheriting-a-red-gate](docs/claude/inheriting-a-red-gate.md), [diagnosing-sv-tests-failures](docs/claude/diagnosing-sv-tests-failures.md), [workflow-worktrees](docs/claude/workflow-worktrees.md).

## Formatting

Run `clang-format -i --style=google` on every file a change touches. It is the one tool to run locally, and it is allowed because it rewrites files rather than judging them: running it produces the bytes that get committed, so it is part of authoring a change rather than part of checking one. The style flag is required because the repository has no `.clang-format` file. Without the flag, clang-format falls back to the LLVM default, reformats whole files and buries the real change.

Longer: [clang-format](docs/claude/clang-format.md).

## Commits and pushes

Commit straight to `main`. There is no pull-request cycle, so CI is the only review buffer there is.

Stage each file by explicit path. `git add -A` and `git add .` sweep untracked scratch directories into history.

`Closes #N`, `Fixes #N` and their variants close the issue the moment the commit lands, brackets or not. Write the closing form as `Closes #N`, one per line: a keyword binds to a single `#N`, so a comma-separated list closes only its first issue. Write `Refs #N` or `See #N` when the commit only mentions an issue.

Add `[skip ci]` only when no workflow is configured to observe the push. The `on:` triggers under `.github/workflows/` decide that, so read them. Do not judge a commit documentary or configurational and assume nothing gates it, because the triggers watch paths rather than kinds of file. `[skip ci]` suppresses every workflow at once, including the one built for the files being changed. Where a path filter already excludes the push, it is redundant besides. When landing several source commits, mark the intermediate ones and leave it off the last, so exactly one matrix run fires.

Describe a change to a shared module in that module's own terms. A docstring, comment, error message or commit message in module M should make sense to a reader who has never heard of anything that calls M.

Write the commit subject at the length that states the change, and leave the body unwrapped. Nothing measures the width of a commit message, and the shorter word chosen to fit a column is paid for out of the accuracy the message exists to carry.

Longer: [pushing-to-main](docs/claude/pushing-to-main.md), [staging-explicit-paths](docs/claude/staging-explicit-paths.md), [issue-closing-keywords](docs/claude/issue-closing-keywords.md), [skipping-ci-runs](docs/claude/skipping-ci-runs.md), [commit-and-docstring-scope](docs/claude/commit-and-docstring-scope.md).

## Issues

Give an issue about the program six sections in a fixed order: "Problem", "Why Unit Tests Did Not Catch It?", "Why Integration Tests Did Not Catch It?", "Why E2E Tests Did Not Catch It?", "Which Unit, Integration, or E2E regression tests would prevent this from happening again?", "Proposed Solution". Write all six every time. Where a tier does not exist for the code in question, say so in its section: that is the finding, and not a reason to drop the section. The regression section names the tests to write, each with its tier and its assertion. It is separate from the solution so that a fix cannot ship with the coverage folded into its last paragraph.

The four test sections belong to the program and to nothing else. The program is what a test tier can run: the C++ and the Python that ship the simulator and the scripts around it. Give an issue about a workflow file, a linter configuration, a build file or the documentation two sections, "Problem" and "Proposed Solution", and no tests. A test over a file no tier runs only reads a value back and asserts what it just read, and it goes red when somebody renames a step. That a module could be extended to police such a file does not make the file program code. `test/` falls on both sides. The machinery a tier runs on is program code and gets six sections, because it can make a whole tier report the wrong answer. The assertions and the fixtures they read get two, since asking why the unit tests did not catch a defective unit test answers itself. What the defect is in decides this, not what the fix touches. Take the vocabulary from the standard, and cite the clause a claim rests on.

Longer: [how-issues-are-written](docs/claude/how-issues-are-written.md).

## Prose

Write the documents in this repository in plain English. State the instruction before the reasoning for it, give each sentence one instruction, and never leave a figure of speech to carry a rule on its own. `docs/tenets/conventions/README.md` states the rule in full, and it governs this file as much as any other.

## Tenets

`docs/tenets/` holds the rules a piece of work is held to, whatever the repository happens to contain: one tree for test suites, one for the documents that state how the work is done. Read the tenets covering what is being touched before writing it, not after. They decide what the work has to do to count, and a change that satisfies every gate can still fail them.

A tenet is generic. It names no language, no tool, no directory and no count, so nothing in it restates what this repository already states correctly elsewhere. Where a tenet and the repository disagree, the repository is what changes. This file is held to the convention tenets in turn: it carries rules, and leaves thresholds, inventories and current shapes to the gate or the tree that decides them.

One tenet has already cost this repository a defect: an input that cannot fail proves nothing. Some values make two quantities coincide, such as an offset and a count at zero, or a position and its name in a range that starts where counting starts. For such a value, code that confuses the two returns the right answer, so every test built on it passes whether the behaviour exists or not. §11.5.1 rules that a declaration decides which bit an index reaches, and that rule went untested for exactly this reason: every test declared its vectors `[N:0]`, where the index and the storage offset are the same number, and two elaborator paths computed offsets where indices were required without one test noticing.

Longer: [docs/tenets/tests/UNIT_TESTS.md](docs/tenets/tests/UNIT_TESTS.md), [docs/tenets/conventions/README.md](docs/tenets/conventions/README.md), [reading-the-tenets](docs/claude/reading-the-tenets.md).

## Tests

Write the tests first, in the same commit as the code they cover. `.github/workflows/scripts.yml` runs `pytest --cov-fail-under=100` over the `unit/` directory of every Python script and library module, so production code without matching unit tests fails on push. Test-first here means authoring order; the red-green observation belongs to CI.

When more than one unit test file covers the same clause, end every file in that family with a letter — `…_11_04_11a.cpp`, `…_11_04_11b.cpp` — and reserve the bare name for a clause that fits in one file. Splitting a one-file clause renames the original to `a`. Run `ls test/src/unit/` for the clause before choosing a suffix: an earlier split may already hold the letter, and writing over that file destroys its cases.

Give a fully-qualified name `Suite.Name` to one declaration only. Each unit test source builds its own executable and `gtest_discover_tests` registers each case into CTest under the bare name, so two files declaring one name give two CTest tests called the same thing, and neither `ctest -R` nor a failure report can tell them apart. Two files covering one rule is fine and often deliberate: an annex file for the BNF production beside a clause file for the prose, or a parser file beside a preprocessor one. The shared name is what breaks, so give each declaration a name stating its own claim rather than dropping the coverage. CI fails on a repeated name.

Write exactly one assertion in a Python test, counting a `with pytest.raises(...)` block as one. A test that raises and then asserts on what the raise left behind counts two and fails `static-analysis`, which gates the pytest jobs, so every one of them reports `skipped` and the push says nothing about whether the change works. Such a test is making two claims. Give each claim its own test, and put the `contextlib.suppress` that lets the failure past into a helper rather than the test body.

Longer: [test-driven-development](docs/claude/test-driven-development.md), [test-file-letter-suffixes](docs/claude/test-file-letter-suffixes.md), [unique-test-names](docs/claude/unique-test-names.md), [one-assert-per-pytest](docs/claude/one-assert-per-pytest.md).

## Reading the LRM

Read `~/LRM.pdf` with the Read tool, one page per call, and wait for each result before issuing the next. Several page reads in one message exhaust a content-filter budget that does not recover for the rest of the turn, after which every tool result is suppressed. Extracting page text through `pypdf` does the same, and reading a very large source file in one call can do it too, so prefer a bounded window or a search.

Printed page number plus one gives the PDF page. [locating-a-clause](docs/claude/locating-a-clause.md) carries a snippet that resolves a clause to a page from the bookmarks without touching page content.

Longer: [reading-the-lrm](docs/claude/reading-the-lrm.md), [oversized-tool-output](docs/claude/oversized-tool-output.md).
