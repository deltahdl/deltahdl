# Notes for Claude sessions in deltahdl

`CLAUDE.md` at the repository root carries the standing conventions in short form and is read at the start of every session. These files carry the longer versions: the reasoning, the incidents that produced each rule, and the details that are needed occasionally rather than constantly. One note per topic, so a session can read the one rule it needs.

These were kept as local memory files until 2026-07-26 and were committed so they survive the machine they were written on. The local copies have been deleted, so these files are the only version there is, and `.claude/settings.json` sets `autoMemoryEnabled` to `false` so that a session cannot start a second copy. Read [where-notes-live](where-notes-live.md) before writing a new note.

## The standard

- [lrm-source-of-truth](lrm-source-of-truth.md) — why `~/LRM.pdf` decides what the code does, and how it shapes structure as well as behaviour
- [reading-the-lrm](reading-the-lrm.md) — one page per tool call, and the content-filter budget that does not recover once spent
- [locating-a-clause](locating-a-clause.md) — resolving a clause to a physical page from the bookmarks, without reading page content

## Working practice

- [oversized-tool-output](oversized-tool-output.md) — one large read can block every later tool result in the turn
- [verifying-through-ci](verifying-through-ci.md) — CI is the default and local is for the inevitable case only
- [inheriting-a-red-gate](inheriting-a-red-gate.md) — fix a red run in the session that finds it, and do not read the conclusion as a verdict
- [clang-format](clang-format.md) — why `--style=google` is not optional
- [diagnosing-sv-tests-failures](diagnosing-sv-tests-failures.md) — run the binary on the file rather than reasoning from the source
- [workflow-worktrees](workflow-worktrees.md) — leave a running workflow's worktrees alone until it reports completion
- [where-notes-live](where-notes-live.md) — a new convention goes in this repository, not in a local memory file

## Prose

These three hold everywhere prose is written here, and not in these notes alone: a reply in a session, an issue body, a commit message, a docstring and a comment in a source file.

- [answer-the-question-asked](answer-the-question-asked.md) — the answer goes in the first sentence, and a check is explained by what makes it fail
- [write-the-exact-name](write-the-exact-name.md) — a name is something the reader can open, and a coined collective noun such as "the machinery" names nothing
- [lead-with-what-it-is-for](lead-with-what-it-is-for.md) — what the thing is for comes before the first identifier, where the reader asked no question

## Commits

- [pushing-to-main](pushing-to-main.md) — direct commits, no pull requests
- [how-issues-are-written](how-issues-are-written.md) — the six sections an issue carries, and why the three test-tier ones are the point
- [issue-blocked-by-sequence](issue-blocked-by-sequence.md) — one linear order over the open issues, with exactly one of them next
- [filing-what-a-session-finds](filing-what-a-session-finds.md) — file the defect the session found, and do not ask first
- [finding-a-subclauses-issues](finding-a-subclauses-issues.md) — a subclause with subclauses beneath it has three issues, and the search finds one
- [issue-closing-keywords](issue-closing-keywords.md) — what closes an issue on push, brackets included
- [staging-explicit-paths](staging-explicit-paths.md) — why `git add -A` is barred
- [commit-and-docstring-scope](commit-and-docstring-scope.md) — describe a shared module's change in that module's own terms

## Code

- [test-driven-development](test-driven-development.md) — tests first, in the same commit, enforced by a 100% coverage gate
- [test-file-letter-suffixes](test-file-letter-suffixes.md) — every file in a split test family ends in a letter, and check the letter first
- [unique-test-names](unique-test-names.md) — one declaration per `Suite.Name`, because CTest registers the bare name and nothing else
- [one-assert-per-pytest](one-assert-per-pytest.md) — `pytest.raises` counts as an assertion, and `assert-one-assert-per-pytest` fails any test function holding two
- [asserting-which-rule-was-reported](asserting-which-rule-was-reported.md) — a test that expects a rejection names the message, the line and the subclause

## Orchestrator scripts

These three are the only home for the rules they carry, since no gate enforces any of them and `CLAUDE.md` says nothing about the scripts they cover. Read them before editing the code that spawns a session: `scripts/satisfy_subclause/mutators.py` and `lib/python/lrm_subclause_dependencies/`, both of which drive `lib/python/claude_cli_streaming`.

- [failing-loudly](failing-loudly.md) — an orchestrator raises instead of skipping past a fatal condition
- [positive-prompts](positive-prompts.md) — write generated prompts as capabilities, not prohibitions
- [naming-pipeline-steps](naming-pipeline-steps.md) — no "Step 0"

## Infrastructure

- [unpinned-ci-toolchain](unpinned-ci-toolchain.md) — everything floats to latest, through composite actions
- [runner-cap-and-the-coverage-gate](runner-cap-and-the-coverage-gate.md) — twenty runners at once, and why the lanes behind `assert-coverage` do not run
