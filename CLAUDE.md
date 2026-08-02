# Working in deltahdl

deltahdl is a SystemVerilog simulator and elaborator pursuing IEEE 1800-2023 conformance. These are the standing conventions for working in this repository. Each section links the longer write-up behind it, one note per topic under `docs/claude/`; [docs/claude/README.md](docs/claude/README.md) indexes them all. A convention learned in a session is added the same way, a section here and a note there, rather than kept in a session's own memory, which travels with one machine and is reviewed by nobody ([where-notes-live](docs/claude/where-notes-live.md)).

## Source of truth

`~/LRM.pdf` (IEEE 1800-2023) decides what the code must do. Check any non-cosmetic change against the relevant clause and make the code conform to the standard rather than to a linter. When a linter and the standard disagree, the standard wins — surface the conflict rather than quietly breaking conformance.

The standard also guides how code is structured. When grouping parameters into a struct, mirror the entities the standard defines for that feature rather than inventing a container of convenience.

Longer: [lrm-source-of-truth](docs/claude/lrm-source-of-truth.md).

## Verification

CI is the source of truth for build and test results. Make the edits, format, commit explicit paths, push to `main`, then read the run with `gh run list` / `gh run view`.

Never build locally, and never run any local tool that CI also runs. There is no inevitability clause: a runtime-invisible coroutine, scheduler or event-watcher bug is read out of the code and the clause, not out of a local print. When a defect really does hide in run-time state, the substitute is a closer reading, not a build.

`clang-format` is the single exception, because it rewrites files rather than judging them — see Formatting below.

This covers every gate. `clang-tidy`, the file-size cap, the `static-analysis` checks and the copy-paste detectors are CI jobs like any other, so a lint sweep is verified by pushing and reading `gh run view --log-failed`. "It is not a build or a test" and "it reproduces in a second" are not exemptions; the tokens spent reading local output are the cost, and CI is free.

A gate whose limits live in a file the repository tracks — a linter configuration, a threshold in the workflow that runs it — is checked against by reading that file, which is what makes running the tool unnecessary rather than merely forbidden.

The Python gates — pytest, the coverage gate, pylint, `mypy --strict`, the one-assert-per-test check, jscpd — all run in `.github/workflows/scripts.yml`. Push and read them there.

A red run belongs to the session that finds it, whoever caused it. A gate that scans the whole tree rather than the diff indicts whoever pushes next by design, so its breach is fixed in the same session and not left as a note for somebody else. Until the jobs that build and test have actually run, a change is unverified: a conclusion of `failure` reads the same whether the change broke something or inherited a break, and a skipped job reports neither pass nor fail. Read the failed log to tell them apart. "Pre-existing failure" is a task, not a disposition.

Longer: [verifying-through-ci](docs/claude/verifying-through-ci.md), [inheriting-a-red-gate](docs/claude/inheriting-a-red-gate.md), [diagnosing-sv-tests-failures](docs/claude/diagnosing-sv-tests-failures.md), [workflow-worktrees](docs/claude/workflow-worktrees.md).

## Formatting

`clang-format -i --style=google` is the one tool to run locally, and the reason it is allowed is that it rewrites files rather than judging them: running it produces the bytes that get committed, so it is part of authoring a change rather than part of checking one. Run it on every touched file. The repository has no `.clang-format` file, so the style flag is required; without it the LLVM default reformats whole files and buries the real change.

Longer: [clang-format](docs/claude/clang-format.md).

## Commits and pushes

Work goes straight to `main` as commits. There is no pull-request cycle, so CI is the only review buffer there is.

Stage each file by explicit path. `git add -A` and `git add .` sweep untracked scratch directories into history.

`Closes #N`, `Fixes #N` and their variants close the issue the moment the commit lands, brackets or not. Write the closing form as `Closes #N`, one per line — a keyword binds to a single `#N`, so a comma-separated list closes only its first issue. Use `Refs #N` or `See #N` when the commit only mentions an issue.

Add `[skip ci]` only when no workflow is configured to observe the push. The `on:` triggers under `.github/workflows/` decide that, and they watch paths rather than kinds of file, so read them instead of judging a commit documentary or configurational and assuming nothing gates it. `[skip ci]` suppresses every workflow at once, including the one built for the files being changed, and a path filter that already excludes the push makes it redundant besides. When landing several source commits, mark the intermediate ones and leave it off the last, so exactly one matrix run fires.

Describe a change to a shared module in that module's own terms. A docstring, comment, error message or commit message in module M should make sense to a reader who has never heard of anything that calls M.

Longer: [pushing-to-main](docs/claude/pushing-to-main.md), [staging-explicit-paths](docs/claude/staging-explicit-paths.md), [issue-closing-keywords](docs/claude/issue-closing-keywords.md), [skipping-ci-runs](docs/claude/skipping-ci-runs.md), [commit-and-docstring-scope](docs/claude/commit-and-docstring-scope.md).

## Issues

An issue about the program has six sections in a fixed order: "Problem", "Why Unit Tests Did Not Catch It?", "Why Integration Tests Did Not Catch It?", "Why E2E Tests Did Not Catch It?", "Which Unit, Integration, or E2E regression tests would prevent this from happening again?", "Proposed Solution". Every such issue has all six; where a tier does not exist for the code in question, saying so is the finding rather than a reason to drop the section. The regression section names the tests to write, each with its tier and its assertion, and is separate from the solution so that a fix cannot ship with the coverage folded into its last paragraph.

The four test sections belong to the program and to nothing else. The program is what a test tier can run: the C++ and the Python that ship the simulator and the scripts around it. An issue about a workflow file, a linter configuration, a build file or the documentation has two sections, "Problem" and "Proposed Solution", and owes no tests — a test over a file no tier runs only reads a value back and asserts what it just read, and goes red when somebody renames a step. That a module could be extended to police such a file does not make the file program code. `test/` falls on both sides: the machinery a tier runs on is program code and gets six, because it can make a whole tier report the wrong answer; the assertions and the fixtures they read get two, since asking why the unit tests did not catch a defective unit test answers itself. What the defect is in decides this, not what the fix touches. Take the vocabulary from the standard and cite the clause a claim rests on.

Longer: [how-issues-are-written](docs/claude/how-issues-are-written.md).

## Tenets

`docs/tenets/` holds the rules a piece of work is held to, whatever the repository happens to contain: one tree for test suites, one for the documents that state how the work is done. Read the tenets covering what is being touched before writing it, not after: they decide what the work has to do to count, and a change that satisfies every gate can still fail them.

A tenet is generic. It names no language, no tool, no directory and no count, so nothing in it restates what this repository already states correctly elsewhere. Where a tenet and the repository disagree, the repository is what changes. This file is held to the convention tenets in turn: it carries rules, and leaves thresholds, inventories and current shapes to the gate or the tree that decides them.

The one that has already cost this repository a defect: an input that cannot fail proves nothing. Where a value makes two quantities coincide — an offset and a count at zero, a position and its name in a range that starts where counting starts — code confusing the two returns the right answer, and every test built on that value passes whether the behaviour exists or not. §11.5.1's rule that a declaration decides which bit an index reaches went untested for exactly this reason: every test declared its vectors `[N:0]`, where the index and the storage offset are the same number, and two elaborator paths computed offsets where indices were required without one test noticing.

Longer: [docs/tenets/tests/UNIT_TESTS.md](docs/tenets/tests/UNIT_TESTS.md), [docs/tenets/conventions/README.md](docs/tenets/conventions/README.md), [reading-the-tenets](docs/claude/reading-the-tenets.md).

## Tests

Tests come first, in the same commit as the code they cover. `.github/workflows/scripts.yml` runs `pytest --cov-fail-under=100` over the `unit/` directory of every Python script and library module, so production code without matching unit tests fails on push. Test-first here means authoring order; the red-green observation belongs to CI.

When more than one unit test file covers the same clause, every file in that family ends in a letter — `…_11_04_11a.cpp`, `…_11_04_11b.cpp` — and the bare name is reserved for a clause that fits in one file. Splitting a one-file clause renames the original to `a`. Check `ls test/src/unit/` for the clause before choosing a suffix: an earlier split may already hold the letter, and writing over that file destroys its cases.

A fully-qualified name `Suite.Name` belongs to one declaration. Each unit test source builds its own executable and `gtest_discover_tests` registers each case into CTest under the bare name, so two files declaring one name give two CTest tests called the same thing: neither `ctest -R` nor a failure report can tell them apart. Two files covering one rule is fine and often deliberate — an annex file for the BNF production beside a clause file for the prose, or a parser file beside a preprocessor one. The shared name is what breaks, so give each declaration a name stating its own claim rather than dropping the coverage. CI fails on a repeated name.

A Python test carries exactly one assertion, and a `with pytest.raises(...)` block is one. A test that raises and then asserts on what the raise left behind counts two and fails `static-analysis`, which gates the pytest jobs, so every one of them reports `skipped` and the push says nothing about whether the change works. Such a test is making two claims: give each its own test, and put the `contextlib.suppress` that lets the failure past into a helper rather than the test body.

Longer: [test-driven-development](docs/claude/test-driven-development.md), [test-file-letter-suffixes](docs/claude/test-file-letter-suffixes.md), [unique-test-names](docs/claude/unique-test-names.md), [one-assert-per-pytest](docs/claude/one-assert-per-pytest.md).

## Reading the LRM

Read `~/LRM.pdf` with the Read tool, one page per call, waiting for each result before the next. Several page reads in one message exhaust a content-filter budget that does not recover for the rest of the turn, after which every tool result is suppressed. Extracting page text through `pypdf` does the same, and reading a very large source file in one call can do it too — prefer a bounded window or a search.

Printed page number plus one gives the PDF page. [locating-a-clause](docs/claude/locating-a-clause.md) carries a snippet that resolves a clause to a page from the bookmarks without touching page content.

Longer: [reading-the-lrm](docs/claude/reading-the-lrm.md), [oversized-tool-output](docs/claude/oversized-tool-output.md).
