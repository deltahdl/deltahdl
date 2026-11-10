# Memories

One fact per file. Each line states its rule, because this index loads every
session and the files are recalled by relevance — see [recording-what-a-session-learns](recording-what-a-session-learns.md).

## Commits and pushes

- [Pushing to main](pushing-to-main.md) — commit straight to `main` and push a finished change without asking.
- [Draining the push queue first](draining-the-push-queue-first.md) — push what sits committed but unpushed before starting new work.
- [Staging explicit paths](git-add-explicit-paths.md) — never `git add -A` or `git add .`; name every path.
- [git add stages nothing when one pathspec misses](git-add-all-or-nothing-pathspecs.md) — never name a removed path to `git add`; it then stages none.
- [Reading the index back](reading-the-index-before-committing.md) — `git status --porcelain` between staging and committing, every time.
- [A commit closes at least one issue](a-commit-closes-an-issue.md) — any number, wherever in the repository they fall, every case of each one's rule passing; split by rule an issue that cannot land in one.
- [Closing keywords fire on push](issue-closing-keywords-fire-on-push.md) — nine words close an issue from anywhere in a message; use them only in the finishing commit.
- [Confirming a push closed its issues](confirming-a-push-closed-its-issues.md) — once the runs are clean, check each issue closed; close by hand where it did not.
- [One closing keyword per issue](one-closing-keyword-per-issue.md) — a keyword binds to one `#N`; repeat it on its own line per issue.
- [A revert does not reopen](a-revert-does-not-reopen.md) — reopen by hand with `gh issue reopen` after reverting the commit that closed it.
- [The form of an issue reference](closing-keyword-form.md) — write `Closes #N` to close, `Refs #N` or `See #N` to mention.
- [No CI-skip directives](no-ci-skip-in-commit-messages.md) — never suppress a run from a commit message; the `on:` triggers already decide.
- [The length of a commit subject](commit-subject-length.md) — a short subject naming the change, the detail in an unwrapped body.
- [Sharing code a change mirrors](sharing-code-a-change-mirrors.md) — share two bodies or tests a change makes equal before pushing; CPD refuses 100 identical tokens.
- [No comments in any file](no-comments-in-any-file.md) — only clang-format's namespace end comments, the six annex headers and inputs whose comment is tested; the why goes in the commit.
- [The module's own terms](module-terms-in-descriptions.md) — write about module M so a reader who has never heard of its callers understands it.
- [New struct members go last](new-struct-members-go-last.md) — tests brace-initialize AST structs by position, so a member inserted earlier shifts them and breaks the build.
- [Per-module elaboration tables are listed twice](per-module-elaboration-tables-are-listed-twice.md) — a new `Elaborator` table goes in `ResetItemElaborationState` and `ItemElaborationStateSaver`.
- [Names say what a thing does](names-say-what-a-thing-does.md) — never a clause, table, figure or annex number or a bare serial.

## Formatting and prose

- [Formatting with clang-format](clang-format-style-flag.md) — `clang-format -i --style=google` on every touched file, from the `llvm@<major>` `install-llvm` defaults to.
- [clang-format on C++ paths only](clang-format-only-cpp-paths.md) — only `.cpp`/`.h`; a CMakeLists.txt fed to it is rewritten as C++ and stops parsing.
- [Ending a scripted function replacement](ending-a-scripted-function-replacement.md) — end the old body at `"\n}\n"` in column 0, never at the first `"}\n"`.
- [Annex files are not edited](annex-files-are-not-edited.md) — `vpi_user.h` is Annex K.2's text byte for byte; a platform shim goes in the build, never in the file.
- [Include what you use](include-what-you-use.md) — include the header declaring each symbol used and none unused, no umbrella headers; an include finding fails the job.
- [Markdown opens with a heading](markdown-top-level-heading.md) — MD041 runs over every Markdown file in the checkout with `--dot`, so the notes are linted too.
- [Accuracy over fitting a column](prose-length-over-column-fitting.md) — never buy a shorter line with a less accurate word; move the text instead.
- [The user's words are restated, never copied](user-words-are-never-recorded-verbatim.md) — everything written carries the user's point in fresh words, never their sentences.

## The LRM

- [Adherence is the goal](adherence-is-the-goal.md) — full adherence to IEEE 1800-2023 is the only aim; never advise a release, a nearer finish line or fewer findings in its place.
- [The LRM is the source of truth](lrm-source-of-truth.md) — check every non-cosmetic change, and every statement of what a clause requires, against the clause; the standard beats the linter.
- [A shall outranks an example and a can](shall-outranks-examples-and-can.md) — §1.5 and §1.10 settle a clash inside the standard; only two equal requirements go to a person.
- [One edition only](single-edition-1800-2023.md) — IEEE 1800-2023 alone; another edition's numbering is translated to 2023 and never carried into deltahdl.
- [The 2017 edition](the-2017-edition.md) — `~/IEEE 1800-2017.pdf`, read only to judge an sv-tests tag in its own edition.
- [No local paths in code or workflows](no-local-paths-in-code-or-workflows.md) — outside `.claude/`, write `IEEE 1800-2023`, never the path `~/IEEE 1800-2023.pdf`.
- [A library is not a standard](a-library-is-not-a-standard.md) — a construct UVM or sv-tests writes against 1800-2023 is reported, never held for a person.
- [The standard's wording belongs to IEEE](lrm-text-is-copyrighted.md) — cite the clause number and paraphrase; never quote the standard's sentences verbatim.
- [The standard guides structure](lrm-guides-structure.md) — mirror the entities the clause defines when grouping parameters into a struct.
- [One LRM page per call](reading-the-lrm-one-page-per-call.md) — one `Read` page per tool call, waiting for each; batching blocks every result in the turn.
- [Never convert the LRM to text](not-converting-the-lrm-to-text.md) — `extract_text()` spends the same budget, and `pdftotext` loses the structure.
- [Standard names listed explicitly](standard-names-listed-explicitly.md) — list and match each mandated name exactly; never a pattern for a closed set, never a decision for the user.
- [Locating a clause](locating-a-clause.md) — the Read tool alone, never `pypdf`; the contents pages at physical 11 to 27, then printed page plus one.
- [Zooming on a formula](zooming-on-a-formula.md) — rasterize a crop with `pdftoppm` at 300 dpi when a glyph is ambiguous in the page rendering.
- [Oversized tool output](oversized-tool-output.md) — read large files in bounded windows; one huge result truncates everything after it.

## Tests

- [Test-driven development](test-driven-development.md) — tests first, in the same commit, each run and seen to fail for its issue's reason before the fix.
- [Fixing a rule in full](fixing-a-rule-in-full.md) — test and fix every allowed and forbidden form of the rule, everywhere and with every operand, in one commit.
- [Inputs that discriminate](discriminating-test-inputs.md) — choose values where incorrect code gives a different answer from correct code.
- [Naming the report in a rejection test](naming-the-report-in-a-rejection-test.md) — use `ReportedError` with message, line and exact `Subclause("…")`.
- [Naming a const local](const-local-naming.md) — `kCamelCase`, or drop the `const`; a `const` reference is a plain `lower_case` variable.
- [One declaration per test name](unique-test-names.md) — each `Suite.Name` in one file only; a CI job fails on duplicates.
- [Rename rather than delete a duplicate](renaming-rather-than-deleting-a-duplicate-test.md) — keep both files covering one rule and qualify the names.
- [A test that constrains a fix](a-test-that-constrains-a-fix.md) — a case failing only on a wrong fix is not redundant; name the wrong fix it catches before deleting it.
- [Letter suffixes on split test files](test-file-letter-suffixes.md) — every file in a split family ends with a letter; the bare name means one file.
- [Check the letter before writing](checking-for-the-letter-before-writing.md) — `ls test/src/unit/` first, or a redirect silently destroys existing cases.
- [A VpiDesignRun SetUp calls the base first](vpi-design-run-setup.md) — an override skipping `VpiDesignRun::SetUp()` builds no VPI model, and its cases read leftovers.
- [The VPI error status is read alone](vpi-error-status-is-read-alone.md) — read `vpi_chk_error` into a local right after the call it checks, never beside another VPI call.
- [Parenthesizing a split-literal array element](parenthesizing-a-split-literal-array-element.md) — wrap each array element made of adjacent string literals in parentheses, or `-Wstring-concatenation` fails the build.
- [No empty test files](no-empty-test-files.md) — a file with no `TEST` fails a job; a new lettered file lands with its first test.
- [Sweeping a citation change](sweeping-a-citation-change.md) — grep the whole tree for the message the diagnostic prints, not only the files named after the old subclause.
- [A braced case's closing brace is a line](braced-case-closing-brace-is-a-line.md) — `case X: { …; break; }` leaves a `}` llvm-cov counts and nothing runs; move the work into a helper.
- [Header templates are covered through the library](header-templates-are-covered-through-the-library.md) — drive one library caller through every branch; a test's own instantiation earns none.
- [A switch needs a reachable default](switch-needs-a-reachable-default.md) — make one real case the `default`, or llvm-cov counts the implicit one as missed.

## Verification

- [Checking locally, then verifying through CI](verifying-through-ci.md) — run locally only what shows a change works: new tests, the rule's test files, `pre-push-checks` over touched files; suite-wide runs are CI's.
- [A rule conforms only when tests show it](a-rule-conforms-only-when-tests-show-it.md) — only a test asserting the standard's outcome shows a case conforms; an untested case is filed.
- [Reading a CI run](reading-a-ci-run.md) — `gh run list --limit 1` before pushing, `gh run view --log-failed` after.
- [Per-line coverage from CI artifacts](per-line-coverage-from-ci-artifacts.md) — read missed lines from the run's coverage artifacts with the local `llvm@<major>` CI ran.
- [Fetching a failed job's log](fetching-a-failed-job-log.md) — when `--log-failed` breaks off or is empty, use `gh api --allow-escape-sequences .../actions/jobs/<id>/logs`.
- [gh run list --commit takes a full SHA](gh-run-list-commit-takes-a-full-sha.md) — pass `$(git rev-parse HEAD)`; a short SHA lists no run.
- [A push that starts no run](a-push-that-starts-no-run.md) — a pushed commit with no check suite gets its run from `gh workflow run deltahdl.yml --ref main`.
- [A push starts a run per workflow](a-push-starts-a-run-per-workflow.md) — one commit can start several runs and `--limit 1` picks one; watch every run the commit lists.
- [Watching a run in the background](watching-a-run-in-the-background.md) — a background shell or a Monitor with `--interval 60`, never a foreground `gh run watch`.
- [Force-cancelling a hung run](force-cancelling-a-hung-run.md) — a hung job ignores a plain cancel; `gh run cancel --force`, then `gh run rerun --failed`.
- [Long-running commands in the background](long-running-commands-in-the-background.md) — anything over about a minute runs with `run_in_background: true`.
- [Waiting while a CI run is in progress](waiting-while-a-ci-run-is-in-progress.md) — only wait: no diagnosis, edits or commits until it lands.
- [Waiting while anything runs in the background](waiting-while-anything-runs-in-the-background.md) — a background command is its turn's last call; until its notification, nothing but waiting, for the issue in hand or any other.
- [Fixing a red run after a push](fixing-a-red-run.md) — fix your push's red run, caused or inherited, in a push of its own first; red only on `assert-coverage` holds nothing up.
- [Gate limits live in tracked files](gate-limits-live-in-tracked-files.md) — read a gate's limit from its tracked config or workflow, not a tool default.
- [Read the sv-tests log first](reading-the-sv-tests-log-first.md) — deltahdl's own output is already under every FAIL line.
- [Fetching an sv-tests file](fetching-an-sv-tests-file.md) — `gh api` against `chipsalliance/sv-tests`, piped through `base64 -d`.
- [sv-tests is a suite](sv-tests-is-a-suite-not-a-corpus.md) — write suite, revision, deltahdl and evaluate; never corpus, runner, score or the tool.

## Scripts and CI mechanisms

- [Failing loudly](failing-loudly-in-orchestrators.md) — an orchestrator under `scripts/` raises or exits non-zero; it never skips and carries on.
- [Positive prompts](positive-prompts.md) — write a generated prompt as the action wanted, not the one forbidden.
- [CI shows all output](ci-shows-all-output.md) — every step prints all its tools say: no quiet flags, no /dev/null.
- [Composite actions](composite-actions.md) — a CI mechanism is `.github/actions/<name>/action.yml`, not a shell script.
- [Naming an inserted step](naming-an-inserted-pipeline-step.md) — give it a real position or a descriptive name, never "Step 0".
- [The unpinned CI toolchain](unpinned-ci-toolchain.md) — everything floats to latest, the runner image too; Actions tags stay at their major version.
- [What an allowlist entry rests on](allowlist-entries-rest-on-a-reading.md) — a name joins a list under `etc/` only for the reason it admits, given in the commit that adds the line.
- [Never weakening a gate](never-weakening-a-gate.md) — fix a red gate in the code: no lowered threshold, disabled check, exempted name or `continue-on-error`.
- [A failing Pages deployment](a-failing-pages-deployment.md) — fixed in the repository's Pages settings (Source: GitHub Actions), never in the workflow.
- [The test clang-tidy config mirrors the source one](clang-tidy-test-config-mirrors-src.md) — change `etc/clang_tidy/src.yml` and `test_src_unit.yml` together.
- [Scans stand on their own](scans-stand-on-their-own.md) — no scanning job needs another or a path detector; each step reporting findings carries `if: ${{ !cancelled() }}`.
- [A workflow's paths name the programs its jobs run](workflow-paths-name-the-programs-its-jobs-run.md) — a tree whose program a job runs goes in the `paths` filter and the `assert-no-comments` trees.
- [The cache budget is two generations](cache-budget-is-two-generations.md) — twice what one run of every cached job stores has to fit in the 10 GB Actions cache.
- [RETRY_TIMEOUT is set generously](retry-timeout-is-generous.md) — install-llvm's per-attempt bound catches a stall; raise it for a long command, never tighten it.

## Issues

- [What does not get filed](what-does-not-get-filed.md) — a case of the rule in hand joins the fix; a case of an open issue's rule joins that issue.
- [Searching for an existing report before filing](searching-for-an-existing-report-before-filing.md) — grep all of src/ and test/ for the rule's own words before filing "not reported".
- [One indivisible problem per issue](one-indivisible-problem-per-issue.md) — one rule with every case listed, or one defect with one fix; split two rules, merge cases of one.
- [Research lives in issues](research-lives-in-issues.md) — file a plan that outlives the session, and each finding, as it arises.
- [Issues have no fixed form](issues-have-no-fixed-form.md) — no house style; write each so a fresh session can act on it alone.
- [Issues carry a standard label and a clause label](issues-carry-a-standard-and-a-clause-label.md) — a standard's issue carries its standard's label and its `§N` or `Annex X`, as does a defect whose fix rewrites a rule's tests; a coverage or harness issue neither.
- [Issue sections take headings](issue-sections-take-headings.md) — open each section of an issue body with `## Heading`, never a bolded first sentence.
- [Guarding an issue body rewrite](guarding-an-issue-body-rewrite.md) — chain fetch, edit and `--body-file` with `&&` and a size check; recover an emptied body through GraphQL `userContentEdits`.
- [Issues define their terms](issues-define-their-terms.md) — say what each file, term and cited clause is and why it is there.
- [Issues state the conclusion](issues-state-conclusions-not-the-trail.md) — a finding that settles a question replaces the options it ruled out.
- [A question the rules answer is not a decision](a-question-the-rules-answer-is-not-a-decision.md) — 'needs decision' only when the reminders, the issue, its links and both standards leave it open; read the whole memory first.
- [Comments from other accounts are ignored](comments-from-other-accounts-are-ignored.md) — only `jdrowne` counts on an issue; anyone else's comment gets no action or reply.
- [gh search returns at most 1000 issues](gh-search-returns-at-most-1000-issues.md) — list open issues with `--limit 10000` and no `--search`, filtering labels in jq.

## Delegation

- [Working without subagents](working-without-subagents.md) — no Agent or Workflow call for any part of the work, unless the user's own message asks for one.

## The notes themselves

- [Where the notes live](note-directories.md) — `.claude/memories/`, one flat directory.
- [Recording what a session learns](recording-what-a-session-learns.md) — one indivisible fact per file, front matter, a line here, Markdown links `[name](name.md)` between files and never `[[name]]`, and no history: the reason, never when or after what.
