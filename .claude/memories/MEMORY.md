# Memories

One fact per file. These lines state the rule rather than name it, because this
index is loaded every session while the files themselves are recalled by
relevance — see [recording-what-a-session-learns](recording-what-a-session-learns.md).

## Commits and pushes

- [Pushing to main](pushing-to-main.md) — commit straight to `main`; there are no pull requests here.
- [Staging explicit paths](git-add-explicit-paths.md) — never `git add -A` or `git add .`; name every path.
- [git add stages nothing when one pathspec misses](git-add-all-or-nothing-pathspecs.md) — never name a removed path to `git add`; it then stages none of them.
- [Reading the index back](reading-the-index-before-committing.md) — `git status --porcelain` between staging and committing, every time.
- [Closing keywords fire on push](issue-closing-keywords-fire-on-push.md) — nine words close an issue from anywhere in a message, brackets included; reserve them for the finishing commit.
- [One closing keyword per issue](one-closing-keyword-per-issue.md) — a keyword binds to one `#N`; repeat it on its own line per issue.
- [A revert does not reopen](a-revert-does-not-reopen.md) — reopen by hand with `gh issue reopen` after reverting the commit that closed it.
- [The form of an issue reference](closing-keyword-form.md) — write `Closes #N` to close, `Refs #N` or `See #N` to mention.
- [No CI-skip directives](no-ci-skip-in-commit-messages.md) — never suppress a run from a commit message; the `on:` triggers already decide.
- [The length of a commit subject](commit-subject-length.md) — state the whole change in the subject; leave the body unwrapped.
- [The module's own terms](module-terms-in-descriptions.md) — write about module M so a reader who has never heard of its callers understands it.

## Formatting and prose

- [Formatting with clang-format](clang-format-style-flag.md) — `clang-format -i --style=google` on every touched file; the style flag is required.
- [Markdown opens with a heading](markdown-top-level-heading.md) — MD041 runs across `**/*.md` with `--dot`, so the notes are linted too.
- [Accuracy over fitting a column](prose-length-over-column-fitting.md) — never buy a shorter line with a less accurate word; move the text instead.

## The LRM

- [The LRM is the source of truth](lrm-source-of-truth.md) — check every non-cosmetic change against the clause; the standard beats the linter.
- [The standard guides structure](lrm-guides-structure.md) — mirror the entities the clause defines when grouping parameters into a struct.
- [One LRM page per call](reading-the-lrm-one-page-per-call.md) — one `Read` page per tool call, waiting for each; batching blocks every result in the turn.
- [Never convert the LRM to text](not-converting-the-lrm-to-text.md) — `extract_text()` spends the same budget, and `pdftotext` loses the structure.
- [Locating a clause](locating-a-clause.md) — walk the `pypdf` bookmarks; printed page is physical page minus one.
- [Oversized tool output](oversized-tool-output.md) — read large files in bounded windows; one huge result truncates everything after it.

## Tests

- [Test-driven development](test-driven-development.md) — tests first, in the same commit; `pytest --cov-fail-under=100` enforces it.
- [Inputs that discriminate](discriminating-test-inputs.md) — choose values where incorrect code gives a different answer from correct code.
- [Naming the report in a rejection test](naming-the-report-in-a-rejection-test.md) — use `ReportedError` with message, line and exact `Subclause("…")`; never a bare "did it fail".
- [Naming a const local](const-local-naming.md) — `kCamelCase`, or drop the `const`; the clang-tidy shards are what say so.
- [One declaration per test name](unique-test-names.md) — each `Suite.Name` in one file only; a CI job fails on duplicates.
- [Rename rather than delete a duplicate](renaming-rather-than-deleting-a-duplicate-test.md) — keep both files covering one rule and qualify the names.
- [Letter suffixes on split test files](test-file-letter-suffixes.md) — every file in a split family ends with a letter; the bare name means one file.
- [Check the letter before writing](checking-for-the-letter-before-writing.md) — `ls test/src/unit/` first, or a redirect silently destroys existing cases.

## Verification

- [Verifying through CI](verifying-through-ci.md) — never build locally, never run a gate CI runs; push and read the run.
- [Reading a CI run](reading-a-ci-run.md) — `gh run list --limit 1` before pushing, `gh run view --log-failed` after.
- [Fixing a red run](fixing-a-red-run.md) — fix it in the session that finds it, whoever caused it.
- [Gate limits live in tracked files](gate-limits-live-in-tracked-files.md) — read the linter config or workflow threshold rather than running the gate.
- [Read the sv-tests log first](reading-the-sv-tests-log-first.md) — the tool's own output is already under every FAIL line.
- [The sv-tests build exception](the-sv-tests-build-exception.md) — build only to run one already-failing file, only for the stdout the log drops.
- [Fetching an sv-tests file](fetching-an-sv-tests-file.md) — `gh api` against `chipsalliance/sv-tests`, piped through `base64 -d`.

## Scripts and CI mechanisms

- [Failing loudly](failing-loudly-in-orchestrators.md) — an orchestrator under `scripts/` raises or exits non-zero; it never skips and carries on.
- [Positive prompts](positive-prompts.md) — write a generated prompt as the action wanted, not the one forbidden.
- [Composite actions](composite-actions.md) — a CI mechanism is `.github/actions/<name>/action.yml`, not a shell script.
- [Naming an inserted step](naming-an-inserted-pipeline-step.md) — give it a real position or a descriptive name, never "Step 0".
- [The unpinned CI toolchain](unpinned-ci-toolchain.md) — everything floats to latest; Actions tags stay at their major version.

## Issues

- [File what the session finds](filing-what-a-session-finds.md) — file it when you find it; do not describe it in a reply and ask.
- [What does not get filed](what-does-not-get-filed.md) — nothing the commit in hand fixes, nothing an open issue already covers.
- [Splitting what one reading found](splitting-what-one-reading-found.md) — a scope that could close alone gets its own issue.

## The notes themselves

- [Where the notes live](note-directories.md) — `.claude/memories/`, one flat directory since 2026-09-07.
- [Recording what a session learns](recording-what-a-session-learns.md) — one indivisible fact per file, front matter, and a line here.
