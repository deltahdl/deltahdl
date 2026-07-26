# Notes for Claude sessions in deltahdl

`CLAUDE.md` at the repository root carries the standing conventions in
short form and is read at the start of every session. This file carries
the longer versions: the reasoning, the incidents that produced each rule,
and the details that are needed occasionally rather than constantly.

These were kept as local memory files until 2026-07-26 and were committed
so they survive the machine they were written on.

## The LRM is the source of truth

`~/LRM.pdf` is a symlink to IEEE 1800-2023, the SystemVerilog standard. It
decides what deltahdl implements. Any change beyond pure cosmetics must be
checked against it and must not conflict with it.

Mechanical lint fixes — enum base types, value initialisation, `auto`,
boolean simplification — are behaviour-preserving and carry no risk. Deeper
fixes do: resolving compile errors, collapsing a duplicate
`CoverageControl` enum, renaming VPI or DPI functions. The VPI names
(`vpi_printf`, `vpi_mcd_*`) and the §40.3 coverage-control constants are
mandated by the standard, and satisfying a linter by renaming them breaks
the conformance the project exists to achieve. When the linter and the
standard disagree, surface the conflict.

The standard also guides how code is structured, not only what it does.
When a refactor groups a function's parameters into a struct — to satisfy
a parameter-count threshold, say — the structs should mirror the entities
the standard defines for that feature. `$readmem` in §21.4 is a file, plus
a target memory (an unpacked array with an element type, per §7.4.3,
§21.4.1 and §21.4.2), plus an optional start and finish window. So the
parameters belong in a `MemTarget` and a `LoadWindow`, not in one struct
of leftovers. The clause citations already in the code comments are the
guide to the right grouping.

## Reading the LRM without blocking the turn

Issue exactly one `Read` page per tool call and wait for each result
before the next. Never put several PDF page reads in one message, and do
not retry in bulk.

Reading the copyrighted standard consumes a content-filter budget. Several
page reads at once exhaust it immediately, and it does not recover by
waiting — around 61 minutes of zero recovery was observed, during which
even `echo hello` had its output suppressed. Once that happens every tool
result in the turn is blocked and no further work is possible until a
fresh turn.

Bulk-extracting page text through `pypdf` — `page.extract_text()` on any
page — blows the same budget, and afterwards even printing the length of
the result is suppressed. The suppression then poisons everything else in
the turn: `echo`, local file reads, all of it.

Do not convert PDFs to text at all. `pdftotext` and friends lose layout,
tables, figures and structure, and produce interleaved text with footers
cut mid-sentence and table columns scrambled. The user objected to
`pdftotext -layout ~/LRM.pdf` on 2026-07-01. The Read tool renders pages
directly and handles figures and tables, and that path survives even after
Bash output has been poisoned.

## Locating a clause in the PDF

`~/LRM.pdf` is IEEE 1800-2023, 1354 PDF pages. The printed page number is
the physical page minus one: §10.1 General is physical page 248, printed
247.

`pdftotext`, `pdfgrep`, `pdftohtml`, `pdftoppm` and `mutool` are blocked by
the Bash deny hook. `pdfinfo` and `python3` with `pypdf` are allowed.
Resolving a clause to a page from the bookmarks reads metadata only, so it
costs nothing against the content-filter budget:

```python
import pypdf
r = pypdf.PdfReader('/Users/jdrowne/LRM.pdf')
def walk(o):
    for it in o:
        if isinstance(it, list):
            walk(it)
            continue
        print(it.title.strip(), '->', r.get_destination_page_number(it) + 1)
walk(r.outline)
```

Then Read the resolved physical pages. Section 10, "Assignment
statements", spans physical pages 248 to 269 and ends at §10.11, "Net
aliasing"; section 11 starts at physical page 270. There is no §10.12,
§10.13 or §10.14.

## Avoiding oversized tool output

One very large tool result can exhaust the same budget that batched PDF
reads do. Reading the roughly 1480-line `src/simulator/vpi.h` in a single
call was enough. After it trips, every later tool result in the turn
renders as `... [truncated]`, including `echo OK`, and it does not recover
within the turn.

That matters because verification depends on reading tool output. Once it
is blocked, the turn cannot be finished.

Read large source files in bounded windows — `Read` with a `limit`, or a
search for the specific symbol — rather than whole-file dumps, and never
pair a large read with other calls in the same batch. If output starts
truncating, stop issuing calls and resume in a fresh turn rather than
working blind.

## Verifying through CI, not locally

The rule, as the user restated it on 2026-06-29: never build or test
locally unless local is inevitable. It is a condition, not a ban with an
exception. CI is the default; local build and test is permitted, with no
separate sign-off, the moment a fix is genuinely un-crackable through CI
iteration. Do not over-ask — when local is inevitable, say so and proceed.

Inevitable means runtime-invisible bugs in coroutines, the scheduler or
event watchers, where every code path reads correctly; commits `27fd32124`
and `2ba1794f1` were cracked locally after about eleven wasted CI rounds.
It also covers full-pipeline output mismatches such as sv-tests failures.
A deterministic lowering, elaborator or evaluation fix is never inevitable
no matter how much regression risk it carries.

The rule is binary, not a trade-off. Two justifications were used and
corrected. "Protect a CI cycle" is not one: CI runs on free GitHub
compute, in parallel, and there is no scarce resource to protect. "Local
caught a regression, so it was worth it" is not one either: if the fix was
not un-crackable, CI would have surfaced the same diff for free.

When local is warranted, use an isolated build directory — for example
`build-seqdebug/`, Ninja and Debug and clang++ — never the pre-existing
`build/`. Instrument with prints, strip all debug output and run
clang-format before committing, and remove the directory afterwards. Note
that `git stash -u` sweeps an untracked build directory into the stash;
use plain `git stash` for before-and-after baselines.

This covers the Python side too. The `scripts/` and `lib/python/` gates —
pytest, the coverage gates, pylint, `mypy --strict`,
`assert-one-assert-per-pytest`, jscpd — all run in
`.github/workflows/scripts.yml` for free. As the user put it: "CI does all
checks. doing things locally costs Claude tokens. CI is free."

The origin of the rule was 2026-06-21, when the documented block on local
builds was rationalised as possibly stale, the user's own `build/` was
reconfigured to get `std::jthread` compiling, full builds were run and
test binaries executed to verify ordinary fixes. The lesson is not that
local is forbidden — it is that going local for routine work CI can verify,
and touching the user's own build directory, are both wrong.

Verify by reading CI: `gh run view`, `gh run list`, and
`gh api repos/deltahdl/deltahdl/actions/jobs/<id>/logs`.

## Formatting with clang-format

Always run `clang-format -i --style=google`. The repository has no
`.clang-format` file, so a bare `clang-format -i` falls back to LLVM
style and reformats the entire file — splitting `if`/`return`, changing
switch indentation — producing a large spurious diff that buries the real
change and fails the gate. CI checks with
`clang-format --dry-run --Werror --style=google`.

If the style flag is missed, `git checkout` the files, re-apply the edits,
and re-format with the flag. Verify with the same `--dry-run --Werror`
command before committing. Note that the formatting gate runs across all
of `src/` and `test/`, so it stays red on pre-existing violations
regardless of the change in hand — check that your own files are clean.

## Pushing to main

The workflow is direct commits to `main`. Do not frame work as pull
requests, do not suggest opening one, and do not structure advice around
review cycles. The user stated it plainly — "we push to main. we dont do
PRs" — and `git log --merges` on `main` is empty.

Use commits as the unit when breaking work down, and think in commit
ordering rather than branch-and-merge. Two consequences follow: a closing
keyword in a commit title fires the moment it is pushed, and CI is the
only review buffer there is.

## Issue-closing keywords in commit messages

GitHub closes any issue referenced as `fix`, `fixes`, `fixed`, `close`,
`closes`, `closed`, `resolve`, `resolves` or `resolved` followed by `#N`,
anywhere in a commit message pushed to the default branch. Brackets do not
disable it: `Fix the gate (#878)` is read as `fix #878` and closes the
issue.

That happened. `Fix implement_subclause's implementability gate (#878)`
was written to reference #878 as the bug being worked on. GitHub closed it
on push, before the verification run had happened, and it had to be
reopened — still visible in the timeline of #878, closed by `be31882e4`
and reopened twelve minutes later.

When a commit only references an issue, use `Refs #N`, `See #N`, a bare
`#N` with no keyword before it, or rephrase the title. Reserve
`Fixes #N` and `Closes #N` for the commit that genuinely finishes the
issue.

## Staging explicit paths

Never use `git add -A` or `git add .`. Stage each file by its path.

The working tree carries untracked scratch directories. One `git add -A`
swept about 112,000 lines of them into commit `9df98e152`, which the user
caught. Recovering meant `git rm -r --cached`, a `.gitignore` entry, an
amend, and a force-push with lease to scrub it from history.

`.claude/` is in `.gitignore` now, but other untracked scratch appears
from time to time, so explicit staging is the rule regardless.

## Skipping CI runs

When a push to `main` needs no CI cycle, include `[skip ci]` (or
`[ci skip]`) in the commit message.

A full matrix run takes 25 to 30 minutes, and `main` is configured with
`cancel-in-progress: true` grouped by ref, so every push otherwise starts
a run and cancels whatever is in flight. Skipping saves the cycle and
protects a running measurement.

Configuration-only and documentation-only commits should carry it. When
batching source fixes, mark the intermediate commits and leave it off the
last so exactly one run fires. Do not skip when the purpose of the push is
to verify, since a CI push is the only verification this repository has.

## Commit and docstring scope

When changing a shared module — `satisfy_subclause.oracles`, for example —
the diff and the commit message must stand on that module's own contract.
Do not name a downstream caller's artifact inside the module's docstrings,
comments, error messages or commit message, even when that caller is what
surfaced the bug.

Commit `de576bda8` was flagged twice for this. First the message anchored
the change in "the cross-chapter cycle in `docs/dependency_graph.json`";
then the docstring of `parse_dependencies` named the same file. Both
treated one caller's symptom as the rationale, when the rule — that
aggregate identifiers are not satisfiable subclauses — applies to every
caller.

Before writing any of those, ask whether it would make sense to a reader
who has never heard of anything that calls the module. If naming a
downstream module is what makes the rationale work, the rationale belongs
in the issue or a cross-cutting document. The standard has the same shape:
a clause that re-presents another subclause's production does not own its
rules.

## Test-driven development

Write the tests first, then the production code that makes them pass. The
user stated "we do TDD", and it is enforced structurally:
`.github/workflows/scripts.yml` runs `pytest --cov-fail-under=100` over
the `unit/` directory of every Python script and library module, so a
commit that adds production code without matching unit tests fails on
push — and there is no pull-request buffer to catch it first.

For every change in `lib/python/`, `scripts/`, or their `test/` trees,
write the unit test under `unit/` before the implementation, in the same
commit. Each module also wants `integration/` and `e2e/` tests, though
those are not coverage-gated. Test-first here means authoring order, not a
local red-green loop: the red and green observations belong to CI, since
pytest is not run locally.

## The 1000-line file cap

CI fails any `.cpp` or `.h` under `src/` or `test/` that exceeds 1000
lines. Splitting a file into cohesive units is the sanctioned remedy —
commit `c30f5c7ce` is the precedent. Do not compress or obfuscate to get
under the cap, and do not avoid a needed change out of fear of the line
count.

Copy the include block into the new file verbatim. `misc-include-cleaner`
is not enabled — it appears nowhere in `etc/clang_tidy/src.yml`,
`etc/clang_tidy/test_src_unit.yml` or `.github/workflows/deltahdl.yml` — so
an over-broad include set carried across from the parent costs nothing,
while pruning includes by hand risks breaking the build.

`src/elaborator/elaborator.h` is a special case: it is one monolithic
`class Elaborator` with nothing else at file scope. A class body cannot be
split across files, so when it reaches the cap the remedy is extraction,
not splitting — pull a cohesive family of methods into its own class and
file. The bodies touch many private members, so the helper needs friend
access or an `Elaborator&`, and the moved methods stop being members.

On 2026-06-28 that header sat at exactly 1000 lines and adding
`ValidateHierRefUndeclaredMember` pushed it to 1004. The stopgap was to
fold the new §23.6 check into the existing
`ValidateHierRefToImportedName`, which has the same signature and walk, so
only one declaration was added. When it next overflows, extract the
scope-rule validators — `ValidateUnresolvedReferences`,
`ValidateHierRef*`, `CheckHierRefUndeclaredMember`, `IsDeclaredNameForRhs`
and `IsNameInModuleScope` — into a `ScopeRuleValidator` for durable
headroom, rather than trimming blank lines again.

## Failing loudly in pipeline code

When something goes wrong inside a pipeline or orchestrator — an oversize
dependency cycle, an unexpected oracle result, a bad dependency — the run
must crash rather than skip the failing item and carry on. Recording
human-resolvable state first is fine and often desirable: label the
issue, write the report file. The very next thing must be a raise, or an
exit with a non-zero code. A plain `return` after a fatal condition is
almost always wrong here.

The user is the one running these orchestrators. Silent partial-success
runs disguise failures, spend tokens on unrelated downstream work, and
leave it ambiguous whether the run finished. A hard failure forces the
question. This was corrected on 2026-04-27, after the oversize-cycle
handler was implemented with a quiet `return` so the orchestrator could
continue to the next descendant.

Reserve quiet returns for the genuinely fine no-op — `commit_mutator_result`
in `satisfy_subclause/mutators.py` returning `False` on an empty diff,
because the subclause was already satisfied.

## Positive phrasing in generated prompts

When writing or editing the prompts this repository's scripts feed to a
spawned session — `build_lrm_read_instruction` and the step pipeline in
`satisfy_subclause/mutators.py`, and the equivalents in `satisfy_clause`,
`satisfy_clauses` and `satisfy_subclauses` — prefer positive instructions
to prohibitions.

Models follow "do X" more reliably than "don't do Y"; negation tends to
surface the prohibited idea without suppressing it. The user pointed this
out after a spawned session bypassed a "Read with the Read tool" hint and
reached for `pypdf` through Bash.

Lead with the capability and how to use it — "The Read tool decodes PDFs
natively; pass `pages: \"N\"` to read page N". Leave prohibitions to an
enforcement layer, such as a PreToolUse hook or a disallowed-tools list.
If a "don't" or "never" is being written into a prompt body, restate it as
the action that is wanted instead.

## Naming pipeline steps

Never name a step "Step 0" when adding to a numbered pipeline. It is an
off-by-one tell: it signals retrofitting rather than redesign, and it
makes the pipeline look as though it always had an unnamed preamble. It
also ages badly, since every later reader has to work out which step
really runs first.

When inserting a step — into `build_steps` in
`scripts/satisfy_subclause/mutators.py`, for instance — either renumber so
the new step takes a real position and the rest shift, or give it a
descriptive name with no number at all.

## Diagnosing sv-tests failures

To root-cause a failing sv-tests file, run the binary on that file. Do not
reason about the failure from the source alone.

On 2026-07-01 reading the code produced two confident hypotheses in a row
— scalar-versus-queue dispatch, then concat-init-not-lowered — and both
were wrong. The actual causes only became visible from the binary's own
output. These are full-pipeline output mismatches, which is exactly the
case that makes local running inevitable, and the user authorised it.

Fetch the file with:

```sh
gh api repos/chipsalliance/sv-tests/contents/tests/chapter-N/<path>.sv \
  --jq .content | base64 -d
```

Then run it from an isolated Debug build directory; `ninja src/deltahdl`
rebuilds incrementally. A file passes when each `:assert:` line reports
equal values.

## Not harvesting a running workflow's worktrees

Do not copy out and `git worktree remove` a workflow's isolated worktrees
until its completion notification actually arrives. Mid-run, `git worktree
list` and per-worktree `git status` can look finished when they are not.

On 2026-06-20 a session was resumed, all thirteen `wf_*` worktrees were
present with uncommitted changes, the header-surgery workflow was assumed
finished, the changes were copied into main as commit `1ce66a18b`, and all
thirteen worktrees were force-removed. The user's interface still showed
"12/13 agents done". The thirteenth agent's worktree was torn down
mid-edit. It happened to have finished its real work and to be writing its
report, so nothing was lost, but it could as easily have been a partial
capture.

Wait for the completion notification — a background workflow re-invokes on
completion, so there is nothing to pre-empt. A `locked` worktree in
`git worktree list` is a strong signal that its agent is still active, and
should never be force-removed as cleanup. If mid-run inspection is
necessary, read only. Worktrees sitting at the base commit with
uncommitted changes is normal for in-flight and finished agents alike, and
proves nothing either way.

## The unpinned CI toolchain

Nothing in CI is pinned; everything floats to latest. The decision was
made on 2026-06-23, prompted by clang-format resolving to v19 in CI while
the local install was v22. It landed on `main` in commits `240075952`,
`b77615a7b` and `d95a32ef0`.

What floats: runner images (`ubuntu-24.04` to `ubuntu-latest`, `macos-26`
to `macos-latest`, on `runs-on:` lines only — the job and artifact name
strings such as `build-ubuntu-24-04-x86-64-clang` are identifiers that
`needs:` and artifact references depend on, and stay as labels). LLVM,
clang, clang-tidy, clang-format, llvm-cov, llvm-profdata, g++ and gcc are
no longer version-suffixed. PMD resolves its latest release through the
GitHub API into a step output with a dynamic cache key.

The mechanism is composite actions, not shell scripts. The first attempt
used raw `scripts/ci/*.sh` and the user rejected it. The house pattern is
`.github/actions/<name>/action.yml` with `using: composite` and
alphabetical keys, as in the sibling repository at
`~/Git/10U-Labs/10ulabs.com`. `install-llvm` and `install-gcc` exist here.
A job uses the action and then has a small `run:` step for ccache, pip or
pmd, since a `uses:` step cannot also `run:`.

One trap is worth remembering. The unversioned apt.llvm.org repository —
`deb http://apt.llvm.org/<codename>/ llvm-toolchain-<codename> main` — is
trunk, not stable, so picking the highest available clang selected 23,
an unreleased development build. Trunk makes the formatting gate
unwinnable, because nightly output drifts and cannot be reproduced off the
runner, and it destabilises clang-tidy. The fix in `b77615a7b` queries
`api.github.com/repos/llvm/llvm-project/releases/latest`, derives the
major version, and adds the stable branch repository
`llvm-toolchain-<codename>-<major> main`. That still follows releases
automatically while staying reproducible.

GitHub Actions tags stay at their major version (`@v5`, `@v4`). Floating
within a major is the safe mechanism; unpinning to a moving ref is a
supply-chain risk. This was flagged to the user and deliberately left
pinned.
