# Notes for Claude sessions in deltahdl

`CLAUDE.md` at the repository root carries the standing conventions in
short form and is read at the start of every session. These files carry
the longer versions: the reasoning, the incidents that produced each rule,
and the details that are needed occasionally rather than constantly. One
note per topic, so a session can read the one rule it needs.

These were kept as local memory files until 2026-07-26 and were committed
so they survive the machine they were written on. The local copies have
been deleted, so these files are the only version there is; see
[where-notes-live](where-notes-live.md) before writing a new note.

## The standard

- [lrm-source-of-truth](lrm-source-of-truth.md) — why `~/LRM.pdf` decides
  what the code does, and how it shapes structure as well as behaviour
- [reading-the-lrm](reading-the-lrm.md) — one page per tool call, and the
  content-filter budget that does not recover once spent
- [locating-a-clause](locating-a-clause.md) — resolving a clause to a
  physical page from the bookmarks, without reading page content

## Working practice

- [oversized-tool-output](oversized-tool-output.md) — one large read can
  block every later tool result in the turn
- [verifying-through-ci](verifying-through-ci.md) — CI is the default and
  local is for the inevitable case only
- [clang-format](clang-format.md) — why `--style=google` is not optional
- [diagnosing-sv-tests-failures](diagnosing-sv-tests-failures.md) — run
  the binary on the file rather than reasoning from the source
- [workflow-worktrees](workflow-worktrees.md) — leave a running
  workflow's worktrees alone until it reports completion
- [where-notes-live](where-notes-live.md) — a new convention goes in this
  repository, not in a local memory file

## Commits

- [pushing-to-main](pushing-to-main.md) — direct commits, no pull requests
- [how-issues-are-written](how-issues-are-written.md) — the six sections
  an issue carries, and why the three test-tier ones are the point
- [issue-closing-keywords](issue-closing-keywords.md) — what closes an
  issue on push, brackets included
- [staging-explicit-paths](staging-explicit-paths.md) — why `git add -A`
  is barred
- [skipping-ci-runs](skipping-ci-runs.md) — when `[skip ci]` belongs in a
  commit message
- [commit-and-docstring-scope](commit-and-docstring-scope.md) — describe
  a shared module's change in that module's own terms

## Code

- [reading-the-tenets](reading-the-tenets.md) — `docs/tenets/` is read
  before the code, and why the tenets say nothing about this repository
- [test-driven-development](test-driven-development.md) — tests first, in
  the same commit, enforced by a 100% coverage gate
- [test-file-letter-suffixes](test-file-letter-suffixes.md) — every file
  in a split test family ends in a letter, and check the letter first
- [unique-test-names](unique-test-names.md) — one declaration per
  `Suite.Name`, because CTest registers the bare name and nothing else
- [one-assert-per-pytest](one-assert-per-pytest.md) — `pytest.raises`
  counts as an assertion, and the gate it fails skips every pytest job

## Orchestrator scripts

These three are the only home for the rules they carry: no gate enforces
any of them, and `CLAUDE.md` says nothing about the subsystem, so read
them before editing code that spawns sessions.

- [failing-loudly](failing-loudly.md) — an orchestrator raises instead of
  skipping past a fatal condition
- [positive-prompts](positive-prompts.md) — write generated prompts as
  capabilities, not prohibitions
- [naming-pipeline-steps](naming-pipeline-steps.md) — no "Step 0"

## Infrastructure

- [unpinned-ci-toolchain](unpinned-ci-toolchain.md) — everything floats to
  latest, through composite actions
