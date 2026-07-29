# Verifying through CI, not locally

The rule, as the user set it on 2026-07-29: never build locally, and never
run any local tool that CI also runs. `clang-format` is the single
exception, and it is an exception because it rewrites files rather than
judging them — running it produces the bytes that get committed, so it is
part of authoring the change, not part of checking it.

Everything else belongs to CI. Build, test, `clang-tidy`, the file-size
cap, the `static-analysis` checks, the copy-paste detectors, and the whole
Python side — pytest, the coverage gates, pylint, `mypy --strict`,
`assert-one-assert-per-pytest` — all run in
`.github/workflows/deltahdl.yml` and `.github/workflows/scripts.yml` for
free. Push and read the run. As the user put it: "CI does all checks. doing
things locally costs Claude tokens. CI is free."

There is no inevitability clause. An earlier version of this note carried
one, permitting a local build for runtime-invisible coroutine, scheduler
and event-watcher bugs. It is gone. The reasoning that retired it: a local
build is easy to justify after the fact, because it always finds something,
and "it caught a regression" is not evidence the regression was invisible
to CI. On 2026-07-29 a local build was configured to localise a scheduler
defect (#2884) and then used to run seven other suites; the most useful
thing it turned up — that the §11.5.1 declared-range fix did not work —
was already on its way from a run that was in flight at that moment. The
local build bought about twenty minutes and cost a full configure plus 290
compilation units.

The same reasoning kills the smaller justifications, which have all been
used and corrected:

- "Protect a CI cycle" — CI runs on free GitHub compute, in parallel, and
  there is no scarce resource to protect.
- "It is not a build or a test" — `clang-tidy` and the file-size cap are CI
  jobs like any other. A red run's `gh run view --log-failed` gives the same
  file/line/check list, for free, and one push verifies every file at once.
- "It reproduces the gate in 1.3 seconds" — the seconds are not the cost.
  The tokens spent reading its output are.
- "Local caught a regression, so it was worth it" — CI would have surfaced
  the same diff for nothing.

What replaces a local probe, when a defect really does hide in run-time
state: read the code and the clause. The two defects closed on 2026-07-29
without any local execution were both found that way — an unqualified call
in a constraint failing because `TryEvalEnclosingInstanceCall` needs both
`CurrentThis()` and `CurrentMethodClass()`, and a `const` at the head of a
subroutine body being eaten as a `tf_port_declaration` because A.2.7 allows
`const` there only before `ref`. Neither needed a print.

Verify by reading CI: `gh run view`, `gh run list`, and
`gh api repos/deltahdl/deltahdl/actions/jobs/<id>/logs`. Never push while a
run is in flight; a push cancels it, so check `gh run list --limit 1` first.
Compare two runs over the intersection of tests with a definite
`Passed`/`***…` result in both, never over failure counts or bare set
differences, and confirm every shard reached its CTest summary.
