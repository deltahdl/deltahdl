# Memories

One fact per file. These lines state the rule rather than name it, because this
index is loaded every session while the files themselves are recalled by
relevance — see [recording-what-a-session-learns](recording-what-a-session-learns.md).

## Commits and pushes

- [Pushing to main](pushing-to-main.md) — commit straight to `main` and push a finished change without asking; there are no pull requests here.
- [One commit is a whole body of work](one-commit-is-a-whole-body-of-work.md) — a push holds a matter solved end to end, or a batch of issues of one matter solved in full, never one step of either.
- [Grouping issues into one push](grouping-issues-into-a-push.md) — every open issue of one clause and one `src/` subsystem, bounded by the matter and never by a count, solved uncommitted and committed once; every comment-only issue is one batch whatever its clause; CI, build, shared-fixture and red-run fixes go alone.
- [Draining the push queue first](draining-the-push-queue-first.md) — while commits sit unpushed, take no new issue; squash them in queue order, never by file-disjointness, and push until none are left.
- [Staging explicit paths](git-add-explicit-paths.md) — never `git add -A` or `git add .`; name every path.
- [git add stages nothing when one pathspec misses](git-add-all-or-nothing-pathspecs.md) — never name a removed path to `git add`; it then stages none of them.
- [Reading the index back](reading-the-index-before-committing.md) — `git status --porcelain` between staging and committing, every time.
- [Closing keywords fire on push](issue-closing-keywords-fire-on-push.md) — nine words close an issue from anywhere in a message, brackets included; reserve them for the finishing commit.
- [Confirming a push closed its issues](confirming-a-push-closed-its-issues.md) — a 64-issue, 103 KB message closed none; once the runs are clean, check each closed and close by hand where it did not take.
- [One closing keyword per issue](one-closing-keyword-per-issue.md) — a keyword binds to one `#N`; repeat it on its own line per issue.
- [A revert does not reopen](a-revert-does-not-reopen.md) — reopen by hand with `gh issue reopen` after reverting the commit that closed it.
- [The form of an issue reference](closing-keyword-form.md) — write `Closes #N` to close, `Refs #N` or `See #N` to mention.
- [No CI-skip directives](no-ci-skip-in-commit-messages.md) — never suppress a run from a commit message; the `on:` triggers already decide.
- [The length of a commit subject](commit-subject-length.md) — state the whole change in the subject; leave the body unwrapped.
- [Sharing code a change mirrors](sharing-code-a-change-mirrors.md) — when a change makes two parallel bodies or two tests equal, share them before pushing; CPD refuses 100 identical tokens.
- [No comments or docstrings in the Python trees](no-comments-or-docstrings-in-python.md) — `assert-no-comments` refuses both under lib/python, scripts, their tests and scripts.yml; the why goes in the commit message.
- [The module's own terms](module-terms-in-descriptions.md) — write about module M so a reader who has never heard of its callers understands it.

## Formatting and prose

- [Formatting with clang-format](clang-format-style-flag.md) — `clang-format -i --style=google` on every touched file; the style flag is required.
- [clang-format on C++ paths only](clang-format-only-cpp-paths.md) — filter the touched paths to `.cpp`/`.h`; a CMakeLists.txt fed to it is rewritten as C++ and stops parsing.
- [Annex files are not edited](annex-files-are-not-edited.md) — `vpi_user.h` is Annex K.2's text byte for byte; a platform shim goes in the build, never in the file.
- [Include what you use](include-what-you-use.md) — name the header that declares each symbol used and none that is unused; no umbrella headers, `vpi_user.h` is Annex K.2's one C file, and an include finding fails the job.
- [Markdown opens with a heading](markdown-top-level-heading.md) — MD041 runs over every Markdown file in the checkout with `--dot`, so the notes are linted too.
- [Accuracy over fitting a column](prose-length-over-column-fitting.md) — never buy a shorter line with a less accurate word; move the text instead.
- [The user's words are restated, never copied](user-words-are-never-recorded-verbatim.md) — memories, issues, commits, comments, tasks and feedback drafts carry the user's point in fresh words, never their sentences quoted or copied.

## The LRM

- [The LRM is the source of truth](lrm-source-of-truth.md) — check every non-cosmetic change against the clause; the standard beats the linter.
- [A shall outranks an example and a can](shall-outranks-examples-and-can.md) — §1.5 and §1.10 settle a clash inside the standard; only two equal requirements go to a person.
- [One edition only](single-edition-1800-2023.md) — IEEE 1800-2023 alone; another edition's numbering is translated to 2023 and never carried into deltahdl.
- [The 2017 edition](the-2017-edition.md) — `~/IEEE 1800-2017.pdf`, read only to judge an sv-tests tag in its own edition.
- [No local paths in code or workflows](no-local-paths-in-code-or-workflows.md) — code, tests, scripts and workflows say `IEEE 1800-2023`; the path `~/IEEE 1800-2023.pdf` is written only under .claude/.
- [A library is not a standard](a-library-is-not-a-standard.md) — a construct the UVM library or sv-tests writes against 1800-2023 is reported, checked in 1800-2023 and 1800.2-2020, never held for a person.
- [The standard's wording belongs to IEEE](lrm-text-is-copyrighted.md) — cite the clause number and paraphrase; never quote the standard's sentences verbatim.
- [The standard guides structure](lrm-guides-structure.md) — mirror the entities the clause defines when grouping parameters into a struct.
- [One LRM page per call](reading-the-lrm-one-page-per-call.md) — one `Read` page per tool call, waiting for each; batching blocks every result in the turn.
- [Never convert the LRM to text](not-converting-the-lrm-to-text.md) — `extract_text()` spends the same budget, and `pdftotext` loses the structure.
- [Standard names listed explicitly](standard-names-listed-explicitly.md) — every name the standard mandates, listed and matched exactly; never a pattern for a closed set, and never a decision to put to the user.
- [Locating a clause](locating-a-clause.md) — the Read tool alone, never `pypdf`; the contents pages at physical 11 to 27, then printed page plus one.
- [Zooming on a formula](zooming-on-a-formula.md) — rasterize a crop with `pdftoppm` at 300 dpi when a glyph is ambiguous in the page rendering.
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
- [A VpiDesignRun SetUp calls the base first](vpi-design-run-setup.md) — an override of `SetUp` that skips `VpiDesignRun::SetUp()` builds no VPI model, and its cases read another case's leftovers.
- [No empty test files](no-empty-test-files.md) — a file with no `TEST` fails a job; a new lettered file lands with its first test.
- [Sweeping a citation change](sweeping-a-citation-change.md) — grep the message the diagnostic prints, across the whole tree; the files named after the old subclause are not the set.

## Verification

- [Verifying through CI](verifying-through-ci.md) — keep local work to what CI has no way to perform; a build, a test binary or a probe of a defect is pushed and read from the run.
- [Reading a CI run](reading-a-ci-run.md) — `gh run list --limit 1` before pushing, `gh run view --log-failed` after.
- [gh run list --commit takes a full SHA](gh-run-list-commit-takes-a-full-sha.md) — pass `$(git rev-parse HEAD)`; a short SHA lists no run, and a watcher waiting on it never ends.
- [Watching a run in the background](watching-a-run-in-the-background.md) — a background shell or a Monitor, never a foreground `gh run watch`.
- [Long-running commands in the background](long-running-commands-in-the-background.md) — anything over about a minute (a `gh` sweep, a CI watch) runs with `run_in_background: true`, then the turn ends; a foreground command holds back every cron reminder.
- [Waiting while a CI run is in progress](waiting-while-a-ci-run-is-in-progress.md) — while any CI run of any workflow is in progress, only wait: no diagnosis, edits or commits until it lands, except preparing comment-only edits.
- [Fixing a red run after a push](fixing-a-red-run.md) — when a push's own run goes red, the pushing session fixes it, caused or inherited, in a push of its own before the next batch.
- [Gate limits live in tracked files](gate-limits-live-in-tracked-files.md) — read the linter config or workflow threshold rather than running the gate.
- [Read the sv-tests log first](reading-the-sv-tests-log-first.md) — deltahdl's own output is already under every FAIL line.
- [Fetching an sv-tests file](fetching-an-sv-tests-file.md) — `gh api` against `chipsalliance/sv-tests`, piped through `base64 -d`.
- [sv-tests is a suite](sv-tests-is-a-suite-not-a-corpus.md) — write suite, revision, deltahdl and evaluate; never corpus, runner, score or the tool.

## Scripts and CI mechanisms

- [Failing loudly](failing-loudly-in-orchestrators.md) — an orchestrator under `scripts/` raises or exits non-zero; it never skips and carries on.
- [Positive prompts](positive-prompts.md) — write a generated prompt as the action wanted, not the one forbidden.
- [Composite actions](composite-actions.md) — a CI mechanism is `.github/actions/<name>/action.yml`, not a shell script.
- [Naming an inserted step](naming-an-inserted-pipeline-step.md) — give it a real position or a descriptive name, never "Step 0".
- [The unpinned CI toolchain](unpinned-ci-toolchain.md) — everything floats to latest; Actions tags stay at their major version.

## Issues

- [Solve what the session finds](solving-what-a-session-finds.md) — file what a session finds as issues of one indivisible problem each; solve one now only if the work in hand cannot go on without it.
- [What does not get filed](what-does-not-get-filed.md) — nothing the commit in hand fixes, nothing an open issue already covers.
- [One indivisible problem per issue](one-indivisible-problem-per-issue.md) — one defect, one fix per issue; an issue found holding two is split there and then.
- [Research lives in issues](research-lives-in-issues.md) — a plan that outlives the session, and each finding it yields, is filed as it arises; the task list and scratchpad are not durable.
- [Issues have no fixed form](issues-have-no-fixed-form.md) — no house style; write each so a fresh session can act on it alone.
- [Issue sections take headings](issue-sections-take-headings.md) — open each section of an issue body with `## Heading`, never a bolded first sentence.
- [Issues define their terms](issues-define-their-terms.md) — say what each file, term and cited clause is and why it is there; never a name the reader must already know.
- [Issues state the conclusion](issues-state-conclusions-not-the-trail.md) — a finding that settles a question replaces the options it ruled out; never append round after round.
- [A question the rules answer is not a decision](a-question-the-rules-answer-is-not-a-decision.md) — 'needs decision' only when the reminders, the issue, its links and both standards (1800-2023 and 1800.2-2020, with the clauses citing or paralleling the rule) leave the question open; order and priority never qualify.

## Tasks

- [One action per task](one-action-per-task.md) — a subject naming several actions is divisible by construction, and so is an umbrella verb like "Solve #N"; count the steps it commits to and split by action.

## Models and delegation

- [Writing code in the main session](writing-code-in-the-main-session.md) — write every code edit in the session itself; a subagent gets none of the scheduled reminders.

## The notes themselves

- [Where the notes live](note-directories.md) — `.claude/memories/`, one flat directory.
- [Recording what a session learns](recording-what-a-session-learns.md) — one indivisible fact per file, front matter, a line here, and no history: the reason, never when or after what.
