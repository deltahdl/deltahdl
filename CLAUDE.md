# Working in deltahdl

deltahdl is a SystemVerilog simulator and elaborator pursuing IEEE 1800-2023 conformance. This file holds the standing conventions for working in this repository. Each section links the longer write-up behind it, one note per topic under `.claude/memories/`, and [.claude/memories/README.md](.claude/memories/README.md) indexes them all. Record a convention learned in a session the same way: a section here and a note there. `.claude/memories/` is tracked by git; do not keep the note in the session tool's local memory directory under `~/.claude/projects/` instead, which travels with one machine and is reviewed by nobody ([where-notes-live](.claude/memories/where-notes-live.md)).

## Source of truth

`~/LRM.pdf` (IEEE 1800-2023) decides what the code must do. Check any non-cosmetic change against the relevant clause, and make the code conform to the standard rather than to a linter. When a linter and the standard disagree, the standard wins. Say so rather than quietly breaking conformance.

The standard also guides how code is structured. When grouping parameters into a struct, mirror the entities the standard defines for that feature rather than inventing a container of convenience.

Longer: [lrm-source-of-truth](.claude/memories/lrm-source-of-truth.md).

## Verification

CI is the source of truth for build and test results. Make the edits, format, commit explicit paths, push to `main`, then read the run with `gh run list` and `gh run view`.

Never build locally, and never run any local tool that CI also runs. Nothing exempts a bug on the grounds that it only shows up while the simulator is running. Find a coroutine, scheduler or event-watcher bug by reading the code and the LRM clause, not by reading a local print. When a defect really does hide in run-time state, read more closely rather than build.

`clang-format` is the single exception, because it rewrites files rather than judging them. See Formatting below.

Every gate is covered by this, not just the build and the tests. `clang-tidy`, the formatting check, the file-size cap, the assertions about suppressions and configuration files, the unit test registration checks and the copy-paste detectors are CI jobs like any other, so verify a lint sweep by pushing and reading `gh run view --log-failed`. Neither "it is not a build or a test" nor "it reproduces in a second" exempts a tool. The cost of running one locally is the tokens spent reading its output, and CI is free.

Some gates take their limits from a file the repository tracks: a linter configuration, or a threshold written into the workflow that runs the tool. Check a change against those limits by reading that file. That is what makes running the tool unnecessary rather than merely forbidden.

The Python gates all run in `.github/workflows/scripts.yml`: pytest, the coverage gate, pylint, `mypy --strict`, the one-assert-per-test check and jscpd. Push and read them there.

Fix a red run in the session that finds it, whoever caused it. A gate that scans the whole tree rather than the diff indicts whoever pushes next by design, so repair its breach in the same session instead of leaving a note about it for somebody else. A change is unverified until the jobs that build and test have actually run. A conclusion of `failure` reads the same whether the change broke something or inherited a break, and a skipped job reports neither pass nor fail. Read the failed log to tell those apart. A pre-existing failure is a task, not a disposition.

Two constraints shape the job graph in `.github/workflows/deltahdl.yml` and appear nowhere in it. The repository runs a fixed number of jobs at once, and that number is smaller than the number of jobs waiting to start, so unblocking a job moves it into a full window rather than into an idle one. The lanes held behind `assert-coverage` are held there deliberately, for the same reason. Measure what a change to the graph displaces before proposing it, and read the note before concluding that a `needs:` is accidental.

Longer: [verifying-through-ci](.claude/memories/verifying-through-ci.md), [inheriting-a-red-gate](.claude/memories/inheriting-a-red-gate.md), [diagnosing-sv-tests-failures](.claude/memories/diagnosing-sv-tests-failures.md), [workflow-worktrees](.claude/memories/workflow-worktrees.md), [runner-cap-and-the-coverage-gate](.claude/memories/runner-cap-and-the-coverage-gate.md).

## Formatting

Run `clang-format -i --style=google` on every file a change touches. It is the one tool to run locally, and it is allowed because it rewrites files rather than judging them: running it produces the bytes that get committed, so it is part of authoring a change rather than part of checking one. The style flag is required because the repository has no `.clang-format` file. Without the flag, clang-format falls back to the LLVM default, reformats whole files and buries the real change.

Longer: [clang-format](.claude/memories/clang-format.md).

## Commits and pushes

Commit straight to `main`. There is no pull-request cycle, so CI is the only review buffer there is.

Stage each file by explicit path. `git add -A` and `git add .` sweep untracked scratch directories into history. Never name a removed path to `git add`, which stages none of its paths when one of them matches nothing on disk. Read the index back with `git status --porcelain` before committing.

`Closes #N`, `Fixes #N` and their variants close the issue the moment the commit lands, brackets or not. Write the closing form as `Closes #N`, one per line: a keyword binds to a single `#N`, so a comma-separated list closes only its first issue. Write `Refs #N` or `See #N` when the commit only mentions an issue.

Never suppress a CI run from a commit message. Let the `on:` triggers under `.github/workflows/` decide which workflows a push needs; they watch paths, and they are already correct about it. A push that changes nothing a workflow watches starts no run, and a push that does change something watched is a push whose run is wanted.

Describe a change to a shared module in that module's own terms. A docstring, comment, error message or commit message in module M should make sense to a reader who has never heard of anything that calls M.

Write the commit subject at the length that states the change, and leave the body unwrapped. Nothing measures the width of a commit message, and the shorter word chosen to fit a column is paid for out of the accuracy the message exists to carry.

Longer: [pushing-to-main](.claude/memories/pushing-to-main.md), [staging-explicit-paths](.claude/memories/staging-explicit-paths.md), [issue-closing-keywords](.claude/memories/issue-closing-keywords.md), [commit-and-docstring-scope](.claude/memories/commit-and-docstring-scope.md).

## Issues

Give an issue about the program six sections in a fixed order: "Problem", "Why Unit Tests Did Not Catch It?", "Why Integration Tests Did Not Catch It?", "Why E2E Tests Did Not Catch It?", "Which Unit, Integration, or E2E regression tests would prevent this from happening again?", "Proposed Solution". Write all six every time. Where a tier does not exist for the code in question, say so in its section: that is the finding, and not a reason to drop the section. The regression section names the tests to write, each with its tier and its assertion. It is separate from the solution so that a fix cannot ship with the coverage folded into its last paragraph.

The four test sections belong to the program and to nothing else. The program is what a test tier can run: the C++ and the Python that ship the simulator and the scripts around it. Give an issue about a workflow file, a linter configuration, a build file or the documentation two sections, "Problem" and "Proposed Solution", and no tests. A test over a file no tier runs only reads a value back and asserts what it just read, and it goes red when somebody renames a step. That a module could be extended to police such a file does not make the file program code. `test/` falls on both sides. The Python and C++ under `test/` that computes the values assertions rest on is program code and gets six sections, because a defect in it can make a whole tier report the wrong answer. The assertions themselves, and the SystemVerilog sources they read, get two, since asking why the unit tests did not catch a defective unit test answers itself. What the defect is in decides this, not what the fix touches. Take the vocabulary from the standard, and cite the clause a claim rests on.

File the issue when the session finds the defect, and do not ask first. A defect described in a reply and nowhere else is gone when the session ends, because the next session reads the repository and the issue tracker and not the transcript. This holds for a defect found while working on something else, which is most of them: finish the work in hand, and file what the reading turned up rather than offering to. A defect the commit in hand fixes needs no issue, and neither does one an open issue already covers; cite that issue instead.

Every open issue numbered above #2939 sits in one linear sequence, ordered by GitHub's blocked-by relation, and exactly one of them is blocked by nothing open. That one is what gets worked next. Put a new issue into the sequence when you create it, by prepending it, appending it, or interposing it between two links, and read its neighbours first so the placement says something true about the order. An issue created with no blocked-by edge leaves two issues claiming to be next.

Give each issue one scope it can close by finishing, and never write an issue that indexes other issues. Such an issue can never leave the sequence, because what it tracks always has something left, and everything behind it waits on the whole programme. Cite another issue wherever it settles something; a citation keeps an issue self-contained, and a list of children is what is barred.

A subclause with a Syntax and a Description beneath it has an issue for each of the three, and `next_subclause` prints the parent. Find the other two by looking up the numbers around it rather than by searching titles, which has returned the parent alone while both children stood open. Close all three in the commit that satisfies them.

Longer: [how-issues-are-written](.claude/memories/how-issues-are-written.md), [issue-blocked-by-sequence](.claude/memories/issue-blocked-by-sequence.md), [filing-what-a-session-finds](.claude/memories/filing-what-a-session-finds.md), [finding-a-subclauses-issues](.claude/memories/finding-a-subclauses-issues.md).

## Prose

Answer the question that was asked, and stop. These rules hold for a reply in a session, an issue body, a commit message, a docstring and a comment in a source file exactly as they hold for a file under `docs/`.

State the instruction before the reasoning for it, give each sentence one instruction, and never leave a figure of speech to carry a rule on its own. `docs/tenets/conventions/README.md` states those three in full for the documents that say how work is done, and it governs this file as much as any other. Here they hold wherever prose is written, and so do the three rules below.

Write every noun that has a name by that name. A name is something the reader can open: a path, a symbol with the source file holding it, a clause of `~/LRM.pdf`, a fully-qualified `Suite.Name`, a CMake target, a job in a workflow file. The coined collective noun is the failure to avoid, because a phrase like "the machinery" or "the layer" reads as vocabulary this repository already uses and sends the reader looking for something that is not there. Say the directory, the source file, the clause or the test case instead. Verify a name before writing it, since a wrong name costs more than a vague one.

Put the answer in the first sentence, and give it the fewest sentences that state it. Add a reason only where the reason changes what the reader would do next, and cut every sentence that is in the draft because it is true rather than because it is needed. Explain a check, a gate or a test by what makes it fail, and say that before anything else about it.

Say what a thing is for before naming its parts, in a document written for a reader who asked no question: an issue body, a note under `docs/`, a docstring. Say what a defect costs in ordinary words near the top rather than in the seventh paragraph. Then cut, because a detail earns its place by changing what somebody would do. Cutting a correct detail is not vagueness; replacing it with a coined noun is.

Nothing enforces any of this. No linter here judges wording, so a green run is not agreement.

Longer: [answer-the-question-asked](.claude/memories/answer-the-question-asked.md), [write-the-exact-name](.claude/memories/write-the-exact-name.md), [lead-with-what-it-is-for](.claude/memories/lead-with-what-it-is-for.md).

## Tenets

`docs/tenets/` holds the rules a piece of work is held to, whatever the repository happens to contain: one tree for test suites, one for the documents that state how the work is done. Read the tenets covering what is being touched before writing it, not after. They decide what the work has to do to count, and a change that satisfies every gate can still fail them.

A tenet is generic. It names no language, no tool, no directory and no count, so nothing in it restates what this repository already states correctly elsewhere. Where a tenet and the repository disagree, the repository is what changes. This file is held to the convention tenets in turn: it carries rules, and leaves thresholds, inventories and current shapes to the gate or the tree that decides them.

One tenet has already cost this repository a defect: an input that cannot fail proves nothing. Some values make two quantities coincide, such as an offset and a count at zero, or a position and its name in a range that starts where counting starts. For such a value, code that confuses the two returns the right answer, so every test built on it passes whether the behaviour exists or not. §11.5.1 rules that a declaration decides which bit an index reaches, and that rule went untested for exactly this reason: every test declared its vectors `[N:0]`, where the index and the storage offset are the same number, and two elaborator paths computed offsets where indices were required without one test noticing.

Longer: [docs/tenets/tests/UNIT_TESTS.md](docs/tenets/tests/UNIT_TESTS.md), [docs/tenets/conventions/README.md](docs/tenets/conventions/README.md), [reading-the-tenets](.claude/memories/reading-the-tenets.md).

## Tests

Write the tests first, in the same commit as the code they cover. `.github/workflows/scripts.yml` runs `pytest --cov-fail-under=100` over the `unit/` directory of every Python script and library module, so production code without matching unit tests fails on push. Test-first here means authoring order; the red-green observation belongs to CI.

When more than one unit test file covers the same subclause, end every file in that family with a letter — `…_11_04_11a.cpp`, `…_11_04_11b.cpp` — and reserve the bare name for a subclause that fits in one file. Splitting a one-file subclause renames the original to `a`. Run `ls test/src/unit/` for the subclause before choosing a suffix: an earlier split may already hold the letter, and writing over that file destroys its cases.

Give a fully-qualified name `Suite.Name` to one declaration only. Each unit test source builds its own executable, and `gtest_discover_tests` registers each case into CTest under the bare name. Two files declaring one name therefore give two CTest tests called the same thing, and neither `ctest -R` nor a failure report can tell them apart. Two files covering one rule is fine and often deliberate: an annex file for the BNF production beside a subclause file for the prose, or a parser file beside a preprocessor one. The shared name is what breaks, so give each declaration a name stating its own claim rather than dropping the coverage. CI fails on a repeated name.

Write exactly one assertion in a Python test, counting a `with pytest.raises(...)` block as one. A test that raises and then asserts on what the raise left behind counts two and fails `assert-one-assert-per-pytest`. No job in `.github/workflows/scripts.yml` waits on that one, so the pytest jobs report whether the change works whatever it finds. Such a test is making two claims. Give each claim its own test, and put the `contextlib.suppress` that lets the failure past into a helper rather than the test body.

A test that expects a source rejected names the report rather than the count, with one call to `ReportedError` in `lib/cpp/test_helpers/helpers_reported_error.h`. It names three things: a substring of the message, the line of the test's own source the report stands at, and the exact `Subclause("…")` text the emission site passes. `EXPECT_TRUE(f.diag.HasErrors())`, `EXPECT_TRUE(f.has_errors)`, `EXPECT_FALSE(ParseOk(...))`, `EXPECT_EQ(..., CompileOutcome::kFailed)`, `ASSERT_EQ(r.diags.size(), 1u)`, `ASSERT_FALSE(r.diags.empty())`, `EXPECT_EQ(f.diag.ErrorCount(), 1U)` and `EXPECT_TRUE(errors)` off an `auto [tokens, errors] = LexWithDiag(…)` binding are each satisfied by any rejection, so a test written for one rule passes when a different rule fired and passes when the source never reached the construct under test. A count is worse than the boolean rather than better: it states how many reports a run made and nothing about which rule any of them enforced, and it goes red when a second report is added for an unrelated reason. `FindDiag` selects a report by its message alone and matches a warning as readily as an error, and `r.diags.front()` is the wrong report to read when a source is rejected twice, so a body reading either names the report through `ReportedError` instead. Where the rule is one the program enforces with a warning, `ReportedWarning` in the same header answers the same three questions. Two kinds of site are not converted: one that varies only the construct under test while holding the rest of the source fixed, where a rejection is already attributable, and one whose rule nothing reports, which needs an issue about the program instead. A test asserting a source was accepted is sound as it stands, since there is no report to name, and so is one that reports the diagnostic itself and reads it back.

Longer: [test-driven-development](.claude/memories/test-driven-development.md), [test-file-letter-suffixes](.claude/memories/test-file-letter-suffixes.md), [unique-test-names](.claude/memories/unique-test-names.md), [one-assert-per-pytest](.claude/memories/one-assert-per-pytest.md), [asserting-which-rule-was-reported](.claude/memories/asserting-which-rule-was-reported.md).

## Reading the LRM

Read `~/LRM.pdf` with the Read tool, one page per call, and wait for each result before issuing the next. Several page reads in one message exhaust a content-filter budget that does not recover for the rest of the turn, after which every tool result is suppressed. Extracting page text through `pypdf` does the same, and reading a very large source file in one call can do it too, so prefer a bounded window or a search.

Printed page number plus one gives the PDF page. [locating-a-clause](.claude/memories/locating-a-clause.md) carries a snippet that resolves a clause to a page from the bookmarks without touching page content.

Longer: [reading-the-lrm](.claude/memories/reading-the-lrm.md), [oversized-tool-output](.claude/memories/oversized-tool-output.md).
