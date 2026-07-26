# Working in deltahdl

deltahdl is a SystemVerilog simulator and elaborator pursuing IEEE 1800-2023
conformance. These are the standing conventions for working in this
repository. Longer write-ups, including the incidents behind several of
these rules, are in `docs/CLAUDE_NOTES.md`.

## Source of truth

`~/LRM.pdf` (IEEE 1800-2023) decides what the code must do. Check any
non-cosmetic change against the relevant clause and make the code conform
to the standard rather than to a linter. When a linter and the standard
disagree, the standard wins — surface the conflict rather than quietly
breaking conformance.

The standard also guides how code is structured. When grouping parameters
into a struct, mirror the entities the standard defines for that feature
rather than inventing a container of convenience.

## Verification

CI is the source of truth for build and test results. Make the edits,
format, commit explicit paths, push to `main`, then read the run with
`gh run list` / `gh run view`.

Build and run tests locally only when CI genuinely cannot settle the
question — runtime-invisible coroutine, scheduler, or event-watcher bugs,
and full-pipeline output mismatches. That case needs no separate sign-off:
say that local is inevitable and proceed. Use an isolated build directory
(Ninja, Debug, clang++), never the pre-existing `build/`, and remove it
when finished. Deterministic lowering, elaborator, and evaluation fixes go
to CI however much regression risk they carry.

The Python gates — pytest, the coverage gate, pylint, `mypy --strict`, the
one-assert-per-test check, jscpd — all run in
`.github/workflows/scripts.yml`. Push and read them there.

## Formatting

`clang-format -i --style=google` is the one tool to run locally by
default. The repository has no `.clang-format` file, so the style flag is
required; without it the LLVM default reformats whole files and buries the
real change.

## Commits and pushes

Work goes straight to `main` as commits. There is no pull-request cycle,
so CI is the only review buffer there is.

Stage each file by explicit path. `git add -A` and `git add .` sweep
untracked scratch directories into history.

`Fixes #N`, `Closes #N` and their variants close the issue the moment the
commit lands, brackets or not. Use `Refs #N` or `See #N` when the commit
only mentions an issue.

Add `[skip ci]` when a commit needs no CI run — configuration-only or
documentation-only changes. When landing several source commits, mark the
intermediate ones and leave it off the last, so exactly one matrix run
fires.

Describe a change to a shared module in that module's own terms. A
docstring, comment, error message or commit message in module M should
make sense to a reader who has never heard of anything that calls M.

## Tests

Tests come first, in the same commit as the code they cover.
`.github/workflows/scripts.yml` runs `pytest --cov-fail-under=100` over
the `unit/` directory of every Python script and library module, so
production code without matching unit tests fails on push. Test-first here
means authoring order; the red-green observation belongs to CI.

## File size

CI fails any `.cpp` or `.h` under `src/` or `test/` over 1000 lines.
Splitting a file into cohesive units is the expected remedy. Copy the
include block across verbatim — `misc-include-cleaner` is not enabled, so
an over-broad include set costs nothing while hand-pruning risks the
build. A class body cannot be split across files, so a header that
outgrows the cap needs a helper class extracted instead.

## Pipeline code

The `satisfy_*` scripts spawn a Claude session per subclause. Three rules
apply to anything running there.

Fail loudly. Record whatever human-resolvable state is needed — label the
issue, write the report — and then raise, or exit non-zero. A quiet
`return` past a fatal condition disguises a partial run as a finished one.

Write the prompts these scripts feed to a session as positive
instructions: lead with the capability and how to use it, and leave
prohibitions to the enforcement layer.

Give a new step in a numbered pipeline a real position or a descriptive
name. "Step 0" signals a retrofit and ages badly.

## Reading the LRM

Read `~/LRM.pdf` with the Read tool, one page per call, waiting for each
result before the next. Several page reads in one message exhaust a
content-filter budget that does not recover for the rest of the turn,
after which every tool result is suppressed. Extracting page text through
`pypdf` does the same, and reading a very large source file in one call
can do it too — prefer a bounded window or a search.

Printed page number plus one gives the PDF page. `docs/CLAUDE_NOTES.md`
carries a snippet that resolves a clause to a page from the bookmarks
without touching page content.
