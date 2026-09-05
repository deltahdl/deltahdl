# Verifying through CI, not locally

Never build locally, and never run any local tool that CI also runs. The user set this rule on 2026-07-29. There are two exceptions, and they are exceptions for different reasons. `clang-format` rewrites files rather than judging them: running it produces the bytes that get committed, so it is part of authoring the change rather than part of checking it. Running the simulator over a single sv-tests file reads something the CI log does not carry, and Diagnosing one sv-tests file below is where that stops.

Push everything else and read the run. Build, test, `clang-tidy`, the formatting check, the file-size cap, the assertions about suppressions and configuration files, the unit test registration checks, the copy-paste detectors and the whole Python side — pytest, the coverage gates, pylint, `mypy --strict`, `assert-one-assert-per-pytest` — all run in `.github/workflows/deltahdl.yml` and `.github/workflows/scripts.yml` for free. As the user put it: "CI does all checks. doing things locally costs Claude tokens. CI is free."

Do not build locally for a bug that only shows up while the simulator is running. An earlier version of this note allowed exactly that, for coroutine, scheduler and event-watcher bugs, and the permission is gone. The sv-tests exception below is not that permission coming back: it is bounded by one named file that a run has already reported failing, and by the single thing the log drops. The reasoning that retired it: a local build always finds something, so it is easy to justify after the fact, and "it caught a regression" is not evidence that the regression was invisible to CI. On 2026-07-29 a local build was configured to localise a scheduler defect and then used to run seven other suites. The most useful thing it turned up — that the §11.5.1 declared-range fix did not work — was already on its way from a run that was in flight at that moment. The local build bought about twenty minutes and cost a full configure plus 290 compilation units.

The same reasoning kills the smaller justifications, which have all been used and corrected:

- "Protect a CI cycle" — CI runs on free GitHub compute, in parallel, and there is no scarce resource to protect.
- "It is not a build or a test" — `clang-tidy` and the file-size cap are CI jobs like any other. A red run's `gh run view --log-failed` gives the same file/line/check list, for free, and one push verifies every file at once.
- "It reproduces the gate in 1.3 seconds" — the seconds are not the cost. The tokens spent reading its output are.
- "Local caught a regression, so it was worth it" — CI would have surfaced the same diff for nothing.

## Diagnosing one sv-tests file

Build the simulator and run it on a single sv-tests file to find out why that file fails. The exception covers one named file that a CI run has already reported failing, run to see what the simulator does with it. It does not cover running the suite, running anything under `test/`, or rebuilding to check whether the fix worked — a fix is verified by pushing, like everything else.

Read the CI log first, because most of the answer is already there. `print_reason` in `scripts/run_sv_tests/__init__.py` prints the tool's own output under every FAIL line, and its docstring gives the reason: "A line naming the file that failed says nothing about why it failed, so whoever picks the failure up has to run the tool over that file themselves to find out -- and working it out from the source instead is a reliable way to reach a confident wrong answer. The output was captured when the test ran; this puts it where the run can be read afterwards." A rejection, the subclause it names, a rejection under a clause other than the one the corpus tags, and an exit that rejected nothing all arrive that way. A file that fails by being rejected therefore needs nothing local at all.

The one thing the log drops is the rest of a simulation's stdout. `run_test` scores a simulated file through `check_assertions`, which walks the `:assert:` lines and returns `Assertion failed: <expr>` for the first that does not hold; every other line the run printed is discarded on the way. When the failing assertion and its two values do not themselves say why they differ, the surrounding output is what says it, and running the file is the only way to see it. That gap is the whole of the exception, and closing it in `run_sv_tests` would end the exception rather than widen it.

[diagnosing-sv-tests-failures](../memories/diagnosing-sv-tests-failures.md) carries how to fetch the file and run it.


When a defect really does hide in run-time state, read the code and the clause instead of probing for it. Two defects were closed that way on 2026-07-29 without running anything. An unqualified call in a constraint failed because `TryEvalEnclosingInstanceCall` needs both `CurrentThis()` and `CurrentMethodClass()`. A `const` at the head of a subroutine body was eaten as a `tf_port_declaration` because A.2.7 allows `const` there only before `ref`. Neither needed a print.

Read the result with `gh run view`, `gh run list` and `gh api repos/deltahdl/deltahdl/actions/jobs/<id>/logs`. Never push while a run is in flight, because a push cancels it; check `gh run list --limit 1` first. Compare two runs over the tests that reported a definite `Passed` or `***…` result in both, never over failure counts or bare set differences, and confirm that every shard reached its CTest summary.
