# Verifying through CI, not locally

Never build locally, and never run any local tool that CI also runs. The user set this rule on 2026-07-29. `clang-format` is the single exception, and it is an exception because it rewrites files rather than judging them: running it produces the bytes that get committed, so it is part of authoring the change rather than part of checking it.

Push everything else and read the run. Build, test, `clang-tidy`, the file-size cap, the `static-analysis` checks, the copy-paste detectors and the whole Python side — pytest, the coverage gates, pylint, `mypy --strict`, `assert-one-assert-per-pytest` — all run in `.github/workflows/deltahdl.yml` and `.github/workflows/scripts.yml` for free. As the user put it: "CI does all checks. doing things locally costs Claude tokens. CI is free."

Do not build locally for a bug that only shows up while the simulator is running. An earlier version of this note allowed exactly that, for coroutine, scheduler and event-watcher bugs, and the permission is gone. The reasoning that retired it: a local build always finds something, so it is easy to justify after the fact, and "it caught a regression" is not evidence that the regression was invisible to CI. On 2026-07-29 a local build was configured to localise a scheduler defect and then used to run seven other suites. The most useful thing it turned up — that the §11.5.1 declared-range fix did not work — was already on its way from a run that was in flight at that moment. The local build bought about twenty minutes and cost a full configure plus 290 compilation units.

The same reasoning kills the smaller justifications, which have all been used and corrected:

- "Protect a CI cycle" — CI runs on free GitHub compute, in parallel, and there is no scarce resource to protect.
- "It is not a build or a test" — `clang-tidy` and the file-size cap are CI jobs like any other. A red run's `gh run view --log-failed` gives the same file/line/check list, for free, and one push verifies every file at once.
- "It reproduces the gate in 1.3 seconds" — the seconds are not the cost. The tokens spent reading its output are.
- "Local caught a regression, so it was worth it" — CI would have surfaced the same diff for nothing.

When a defect really does hide in run-time state, read the code and the clause instead of probing for it. Two defects were closed that way on 2026-07-29 without running anything. An unqualified call in a constraint failed because `TryEvalEnclosingInstanceCall` needs both `CurrentThis()` and `CurrentMethodClass()`. A `const` at the head of a subroutine body was eaten as a `tf_port_declaration` because A.2.7 allows `const` there only before `ref`. Neither needed a print.

Read the result with `gh run view`, `gh run list` and `gh api repos/deltahdl/deltahdl/actions/jobs/<id>/logs`. Never push while a run is in flight, because a push cancels it; check `gh run list --limit 1` first. Compare two runs over the tests that reported a definite `Passed` or `***…` result in both, never over failure counts or bare set differences, and confirm that every shard reached its CTest summary.
